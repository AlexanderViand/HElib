/* Copyright (C) 2012-2017 IBM Corp.
 * This program is Licensed under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance
 * with the License. You may obtain a copy of the License at
 *   http://www.apache.org/licenses/LICENSE-2.0
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License. See accompanying LICENSE file.
 */
#include <iostream>
#include <fstream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <NTL/BasicThreadPool.h>
#include <numeric>

NTL_CLIENT

#include "../EncryptedArray.h"
#include "../FHE.h"

#include "../intraSlot.h"
#include "../binaryArith.h"

#ifdef DEBUG_PRINTOUT

#include "../debugging.h"

#endif
// define flags FLAG_PRINT_ZZX, FLAG_PRINT_POLY, FLAG_PRINT_VEC, functions
//        decryptAndPrint(ostream, ctxt, sk, ea, flags)
//        decryptAndCompare(ctxt, sk, ea, pa);

static std::vector<zzX> unpackSlotEncoding; // a global variable
static bool verbose = false;

static long mValues[][15] = {
// { p, phi(m),   m,   d, m1, m2, m3,    g1,   g2,   g3, ord1,ord2,ord3, B,c}
        {2, 48,    105,   12, 3,    35,  0,   71,    76,    0,     2,   2,   0,   25, 2},
        {2, 600,   1023,  10, 11,   93,  0,   838,   584,   0,     10,  6,   0,   25, 2},
        {2, 2304,  4641,  24, 7,    3,   221, 3979,  3095,  3760,  6,   2,   -8,  25, 3},
        {2, 5460,  8193,  26, 8193, 0,   0,   46,    0,     0,     210, 0,   0,   25, 3},
        {2, 8190,  8191,  13, 8191, 0,   0,   39,    0,     0,     630, 0,   0,   25, 3},
        {2, 10752, 11441, 48, 17,   673, 0,   4712,  2024,  0,     16,  -14, 0,   25, 3},
        {2, 15004, 15709, 22, 23,   683, 0,   4099,  13663, 0,     22,  31,  0,   25, 3},
        {2, 27000, 32767, 15, 31,   7,   151, 11628, 28087, 25824, 30,  6,   -10, 28, 4}
};

int main(int argc, char *argv[]) {
    ArgMapping amap;
    long prm = 7;
    amap.arg("prm", prm, "parameter size (0-tiny,...,7-huge)");
    long bitSize = 8;
    amap.arg("bitSize", bitSize, "bitSize of input integers (<=32)");
    bool bootstrap = false;
    amap.arg("bootstrap", bootstrap, "test multiplication with bootstrapping");
    long seed = 0;
    amap.arg("seed", seed, "PRG seed");
    long nthreads = 4;
    amap.arg("nthreads", nthreads, "number of threads");
    amap.arg("verbose", verbose, "print more information");
    amap.parse(argc, argv);
    if (seed) NTL::SetSeed(ZZ(seed));
    if (nthreads > 1) NTL::SetNumThreads(nthreads);

    if (bitSize <= 0) bitSize = 5;
    else if (bitSize > 32) bitSize = 32;

    long *vals = mValues[prm];
    long p = vals[0];
    //  long phim = vals[1];
    long m = vals[2];

    NTL::Vec<long> mvec;
    append(mvec, vals[4]);
    if (vals[5] > 1) append(mvec, vals[5]);
    if (vals[6] > 1) append(mvec, vals[6]);

    std::vector<long> gens;
    gens.push_back(vals[7]);
    if (vals[8] > 1) gens.push_back(vals[8]);
    if (vals[9] > 1) gens.push_back(vals[9]);

    std::vector<long> ords;
    ords.push_back(vals[10]);
    if (abs(vals[11]) > 1) ords.push_back(vals[11]);
    if (abs(vals[12]) > 1) ords.push_back(vals[12]);

    long B = vals[13];
    long c = vals[14];

    // Compute the number of levels
    long L;
    if (bootstrap) L = 30; // that should be enough
    else {
        double add2NumsLvls = log(bitSize) / log(2.0);
        double squareLvls = log(2 * bitSize) / log(2.0);
        double internalAddLvls = 2; // just a guess
        double internalMinLvls = 2; // just a guess
        L = 3 + ceil(add2NumsLvls + squareLvls + internalAddLvls + internalMinLvls);
    }

    if (verbose) {
        cout << "input bitSizes=" << bitSize << ",";
        if (nthreads > 1) cout << " using " << NTL::AvailableThreads() << " threads\n";
        cout << "computing key-independent tables..." << std::flush;
    }
    FHEcontext context(m, p, /*r=*/1, gens, ords);
    context.bitsPerLevel = B;
    buildModChain(context, L, c,/*extraBits=*/8);
    if (bootstrap) {
        context.makeBootstrappable(mvec, /*t=*/0,
                /*flag=*/false, /*cacheType=DCRT*/2);
    }
    buildUnpackSlotEncoding(unpackSlotEncoding, *context.ea);
    if (verbose) {
        cout << " done.\n";
        context.zMStar.printout();
        cout << " L=" << L << ", B=" << B << endl;
        cout << "\ncomputing key-dependent tables..." << std::flush;
    }
    FHESecKey secKey(context);
    secKey.GenSecKey(/*Hweight=*/128);
    addSome1DMatrices(secKey); // compute key-switching matrices
    addFrbMatrices(secKey);
    if (bootstrap) secKey.genRecryptData();
    if (verbose) cout << " done\n";

    activeContext = &context; // make things a little easier sometimes
#ifdef DEBUG_PRINTOUT
    dbgEa = (EncryptedArray *) context.ea;
    dbgKey = &secKey;
#endif



    ////////////////////////////////// START TEST //////////////////////////

    const EncryptedArray &ea = *(secKey.getContext().ea);

    // Choose a vector of random numbers
    long active_slots = 128;
    assert(2 * active_slots <= ea.size());
    std::vector<long> pa(ea.size(), 1);
    std::vector<long> pb(ea.size(), 1);
    for (long i = 0; i < 2 * active_slots; ++i) {
        pa[i] = RandomBits_long(bitSize);
        pb[i] = RandomBits_long(bitSize);
#ifdef  DEBUG_PRINTOUT
        cout << "pa[" << i << "]: " << pa[i] << endl;
        cout << "pb[" << i << "]: " << pb[i] << endl;
#endif
    }

    // Encrypt the individual bits
    NTL::Vec<Ctxt> eSum, enca, encb;

    resize(enca, bitSize, Ctxt(secKey));
    resize(encb, bitSize, Ctxt(secKey));
    for (long i = 0; i < bitSize; i++) {
        std::vector<long> t_pa = pa;
        std::vector<long> t_pb = pb;
        for (long &l : t_pa) {
            l = (l >> i) & 1;
        }
        for (long &l : t_pb) {
            l = (l >> i) & 1;
        }
        ea.skEncrypt(enca[i], secKey, t_pa);
        ea.skEncrypt(encb[i], secKey, t_pb);
        if (bootstrap) {
            // put them at a lower level
            enca[i].modDownToLevel(5);
            encb[i].modDownToLevel(5);
        }
    }

    if (verbose) {
        cout << "\n  bits-size " << bitSize << endl;
        CheckCtxt(enca[0], "b4 addition");
    }

    /////////// ADDITION
    vector<long> slots;
    // Outsize == bitsize because only then does two's complement addition work properly!
    {
        CtPtrs_VecCt eep(eSum);  // A wrapper around the output vector
        addTwoNumbers(eep, CtPtrs_VecCt(enca), CtPtrs_VecCt(encb),
                      bitSize, &unpackSlotEncoding);
        decryptBinaryNums(slots, eep, secKey, ea);
    } // get rid of the wrapper
    if (verbose) CheckCtxt(eSum[lsize(eSum) - 1], "after addition");
    long test_slot = 0;
    long pSum = pa[test_slot] + pb[test_slot];
//  if (slots[0] != ((pa[test_slot]+pb[test_slot]))) {
////    cout << "addTwoNums error: pa="<<pa[test_slot]<<", pb="<<pb[test_slot]
////         << ", but pSum="<<slots[0]
////         << " (should be ="<<(pSum)<<")\n";
////    exit(0);
////  }
////  else
    if (verbose) {
        cout << "addTwoNums succeeded: " << pa[test_slot] << "+" << pb[test_slot] << "=" << slots[0] << endl;
    }

    ///////// SQUARING (currently just a sign-extended standard multiplication)

    // Duplicate the output
    NTL::Vec<Ctxt> eSum2 = eSum;
    // Sign-extend the numbers
    int newSize = 2 * bitSize;
    resize(eSum, newSize, eSum[bitSize - 1]);
    resize(eSum2, newSize, eSum2[bitSize - 1]);

    // Now multiply
    long pProd = slots[test_slot] * slots[test_slot];
    // Test positive multiplication
    NTL::Vec<Ctxt> eProduct;
    {
        CtPtrs_VecCt eep(eProduct);  // A wrappers around the output vector
        multTwoNumbers(eep, CtPtrs_VecCt(eSum), CtPtrs_VecCt(eSum2),/*negative=*/false,
                       2 * bitSize, &unpackSlotEncoding);
        decryptBinaryNums(slots, eep, secKey, ea);
    } // get rid of the wrapper
    if (verbose)
        CheckCtxt(eProduct[lsize(eProduct) - 1], "after multiplication");

    if (slots[0] != pProd) {
        cout << "Positive product error" << endl;
        exit(0);
    } else if (verbose) {
        cout << "positive product succeeded: " << endl;
    }

    ////////// INTERNAL ADD
    NTL::Vec<Ctxt> eIntSum;
    long pIntSum = std::accumulate(slots.begin(), slots.begin() + active_slots, 0l);
    // Test internal addition
    {
        CtPtrs_VecCt eep(eIntSum);  // A wrapper around the output vector
        internalAdd(eep, CtPtrs_VecCt(eProduct), active_slots, &unpackSlotEncoding);
        decryptBinaryNums(slots, eep, secKey, ea);
    } // get rid of the wrapper
    if (verbose) CheckCtxt(eSum[lsize(eSum) - 1], "after internal addition");


//    if (slots[test_slot] != ((pIntSum))) {
//        cout << "internal add error: pIntSum=" << slots[0]
//             << " (should be =" << (pIntSum) << ")\n";
//        exit(0);
//    } else
    if (verbose) {
        cout << "internal add succeeded: " << slots[test_slot] << endl;
    }


    ////////// INTERNAL MIN
    // Test internal sort
    // Create the indices

    // For the indices, find out how many bits we need:
    long bits = _ntl_g2logs(ea.size() / active_slots + 1);
    // Generate the fitting index at each position
    vector<long> pIndices(ea.size(), 1); //using 1 instead of 0 to make errors easier to spot
    int index = 0;
    for (int i = 0; i < ea.size(); ++i) {
        if (i % active_slots == 0) {
            pIndices[i] = index;
            ++index;
        }
    }

    NTL::Vec<Ctxt> eIndices;
    // Encode them
    resize(eIndices, bits, Ctxt(secKey));
    for (long i = 0; i < bits; i++) {
        std::vector<long> t = pIndices;
        for (long &l : t) {
            l = (l >> i) & 1;
        }
        ZZX zzx_t;
        ea.encode(zzx_t, t);
        eIndices[i].DummyEncrypt(zzx_t);
        if (bootstrap) {
            // put them at a lower level
            eIndices[i].modDownToLevel(5);
        }
    }

    vector<long> v_slots;
    vector<long> i_slots;
    { // Wrapper
        CtPtrs_VecCt eev(eIntSum);
        CtPtrs_VecCt eei(eIndices);
        internalMin(eev, eei, active_slots, &unpackSlotEncoding);
        decryptBinaryNums(v_slots, eev, secKey, ea);
        decryptBinaryNums(i_slots, eei, secKey, ea);
    }
    if (verbose) CheckCtxt(eIntSum[lsize(eIntSum) - 1], "after internal min");

    //TODO: Check min result


    return 0;
}


void testProduct(FHESecKey &secKey, long bitSize, long bitSize2,
                 long outSize, bool bootstrap) {
    const EncryptedArray &ea = *(secKey.getContext().ea);
    long mask = (outSize ? ((1L << outSize) - 1) : -1);

    // Choose two random n-bit integers
    long pa = RandomBits_long(bitSize);
    long pb = RandomBits_long(bitSize2);

    // Encrypt the individual bits
    NTL::Vec<Ctxt> eProduct, enca, encb;

    resize(enca, bitSize, Ctxt(secKey));
    for (long i = 0; i < bitSize; i++) {
        secKey.Encrypt(enca[i], ZZX((pa >> i) & 1));
        if (bootstrap) { // put them at a lower level
            enca[i].modDownToLevel(5);
        }
    }
    resize(encb, bitSize2, Ctxt(secKey));
    for (long i = 0; i < bitSize2; i++) {
        secKey.Encrypt(encb[i], ZZX((pb >> i) & 1));
        if (bootstrap) { // put them at a lower level
            encb[i].modDownToLevel(5);
        }
    }
    if (verbose) {
        cout << "\n  bits-size " << bitSize << '+' << bitSize2;
        if (outSize > 0) cout << "->" << outSize;
        CheckCtxt(encb[0], "b4 multiplication");
    }
    // Test positive multiplication
    vector<long> slots;
    {
        CtPtrs_VecCt eep(eProduct);  // A wrappers around the output vector
        multTwoNumbers(eep, CtPtrs_VecCt(enca), CtPtrs_VecCt(encb),/*negative=*/false,
                       outSize, &unpackSlotEncoding);
        decryptBinaryNums(slots, eep, secKey, ea);
    } // get rid of the wrapper
    if (verbose)
        CheckCtxt(eProduct[lsize(eProduct) - 1], "after multiplication");
    long pProd = pa * pb;
    if (slots[0] != ((pa * pb) & mask)) {
        cout << "Positive product error: pa=" << pa << ", pb=" << pb
             << ", but product=" << slots[0]
             << " (should be " << pProd << '&' << mask << '=' << (pProd & mask) << ")\n";
        exit(0);
    } else if (verbose) {
        cout << "positive product succeeded: ";
        if (outSize) cout << "bottom " << outSize << " bits of ";
        cout << pa << "*" << pb << "=" << slots[0] << endl;
    }
    // Test negative multiplication
    secKey.Encrypt(encb[bitSize2 - 1], ZZX(1));
    decryptBinaryNums(slots, CtPtrs_VecCt(encb), secKey, ea, /*negative=*/true);
    pb = slots[0];
    eProduct.kill();
    {
        CtPtrs_VecCt eep(eProduct);  // A wrappers around the output vector
        multTwoNumbers(eep, CtPtrs_VecCt(enca), CtPtrs_VecCt(encb),/*negative=*/true,
                       outSize, &unpackSlotEncoding);
        decryptBinaryNums(slots, eep, secKey, ea, /*negative=*/true);
    } // get rid of the wrapper
    if (verbose)
        CheckCtxt(eProduct[lsize(eProduct) - 1], "after multiplication");
    pProd = pa * pb;
    if ((slots[0] & mask) != (pProd & mask)) {
        cout << "Negative product error: pa=" << pa << ", pb=" << pb
             << ", but product=" << slots[0]
             << " (should be " << pProd << '&' << mask << '=' << (pProd & mask) << ")\n";
        exit(0);
    } else if (verbose) {
        cout << "negative product succeeded: ";
        if (outSize) cout << "bottom " << outSize << " bits of ";
        cout << pa << "*" << pb << "=" << slots[0] << endl;
    }

#ifdef DEBUG_PRINTOUT
    const Ctxt *minCtxt = nullptr;
    long minLvl = 1000;
    for (const Ctxt &c: eProduct) {
        long lvl = c.findBaseLevel();
        if (lvl < minLvl) {
            minCtxt = &c;
            minLvl = lvl;
        }
    }
    decryptAndPrint((cout << " after multiplication: "), *minCtxt, secKey, ea, 0);
    cout << endl;
#endif
}


void testAdd(FHESecKey &secKey, long bitSize1, long bitSize2,
             long outSize, bool bootstrap) {
    const EncryptedArray &ea = *(secKey.getContext().ea);
    long mask = (outSize ? ((1L << outSize) - 1) : -1);

    // Choose two random n-bit integers
    long pa = RandomBits_long(bitSize1);
    long pb = RandomBits_long(bitSize2);

    // Encrypt the individual bits
    NTL::Vec<Ctxt> eSum, enca, encb;

    resize(enca, bitSize1, Ctxt(secKey));
    for (long i = 0; i < bitSize1; i++) {
        secKey.Encrypt(enca[i], ZZX((pa >> i) & 1));
        if (bootstrap) { // put them at a lower level
            enca[i].modDownToLevel(5);
        }
    }
    resize(encb, bitSize2, Ctxt(secKey));
    for (long i = 0; i < bitSize2; i++) {
        secKey.Encrypt(encb[i], ZZX((pb >> i) & 1));
        if (bootstrap) { // put them at a lower level
            encb[i].modDownToLevel(5);
        }
    }
    if (verbose) {
        cout << "\n  bits-size " << bitSize1 << '+' << bitSize2;
        if (outSize > 0) cout << "->" << outSize;
        cout << endl;
        CheckCtxt(encb[0], "b4 addition");
    }

    // Test addition
    vector<long> slots;
    {
        CtPtrs_VecCt eep(eSum);  // A wrapper around the output vector
        addTwoNumbers(eep, CtPtrs_VecCt(enca), CtPtrs_VecCt(encb),
                      outSize, &unpackSlotEncoding);
        decryptBinaryNums(slots, eep, secKey, ea);
    } // get rid of the wrapper
    if (verbose) CheckCtxt(eSum[lsize(eSum) - 1], "after addition");
    long pSum = pa + pb;
    if (slots[0] != ((pa + pb) & mask)) {
        cout << "addTwoNums error: pa=" << pa << ", pb=" << pb
             << ", but pSum=" << slots[0]
             << " (should be =" << (pSum & mask) << ")\n";
        exit(0);
    } else if (verbose) {
        cout << "addTwoNums succeeded: ";
        if (outSize) cout << "bottom " << outSize << " bits of ";
        cout << pa << "+" << pb << "=" << slots[0] << endl;
    }

#ifdef DEBUG_PRINTOUT
    const Ctxt *minCtxt = nullptr;
    long minLvl = 1000;
    for (const Ctxt &c: eSum) {
        long lvl = c.findBaseLevel();
        if (lvl < minLvl) {
            minCtxt = &c;
            minLvl = lvl;
        }
    }
    decryptAndPrint((cout << " after addition: "), *minCtxt, secKey, ea, 0);
    cout << endl;
#endif
}


void testInternalAdd(FHESecKey &secKey, long bitSize,
                     long outSize, bool bootstrap) {
    const EncryptedArray &ea = *(secKey.getContext().ea);
    long mask = (outSize ? ((1L << outSize) - 1) : -1);

    // Choose a vector of random numbers
    long active_slots = 17;
    assert(2 * active_slots <= ea.size());
    std::vector<long> pa(ea.size(), 1);
    for (long i = 0; i < 2 * active_slots; ++i) {
        pa[i] = RandomBits_long(bitSize);
#ifdef  DEBUG_PRINTOUT
        cout << "pa[" << i << "]: " << pa[i] << endl;
#endif

    }

    // Encrypt the individual bits
    NTL::Vec<Ctxt> eSum, enca;

    resize(enca, bitSize, Ctxt(secKey));
    for (long i = 0; i < bitSize; i++) {
        std::vector<long> t_pa = pa;
        for (long &l : t_pa) {
            l = (l >> i) & 1;
        }
        ea.skEncrypt(enca[i], secKey, t_pa);
        if (bootstrap) {
            // put them at a lower level
            enca[i].modDownToLevel(5);
        }
    }

    if (verbose) {
        cout << "\n  bits-size " << bitSize;
        if (outSize > 0) cout << "->" << outSize;
        cout << endl;
        CheckCtxt(enca[0], "b4 internal addition");
    }

    // Test internal addition
    vector<long> slots;
    {
        CtPtrs_VecCt eep(eSum);  // A wrapper around the output vector
        internalAdd(eep, CtPtrs_VecCt(enca), active_slots, &unpackSlotEncoding);
        decryptBinaryNums(slots, eep, secKey, ea);
    } // get rid of the wrapper
    if (verbose) CheckCtxt(eSum[lsize(eSum) - 1], "after internal addition");
    long pSum = std::accumulate(pa.begin() + active_slots, pa.begin() + 2 * active_slots, 0);

    if (slots[active_slots] != ((pSum) & mask)) {
        cout << "internal add error: pSum=" << slots[0]
             << " (should be =" << (pSum & mask) << ")\n";
        exit(0);
    } else if (verbose) {
        cout << "internal add succeeded: ";
        if (outSize)
            cout << "bottom " << outSize << " bits of sum = "
                 << slots[active_slots] << endl;
    }

#ifdef DEBUG_PRINTOUT
    const Ctxt *minCtxt = nullptr;
    long minLvl = 1000;
    for (const Ctxt &c: eSum) {
        long lvl = c.findBaseLevel();
        if (lvl < minLvl) {
            minCtxt = &c;
            minLvl = lvl;
        }
    }
    decryptAndPrint((cout << " after internal addition: "), *minCtxt, secKey, ea, 0);
    cout << endl;
#endif
}

void testInternalMin(FHESecKey &secKey, long bitSize, bool bootstrap) {
    const EncryptedArray &ea = *(secKey.getContext().ea);

    // Choose a vector of random numbers
    long interval = 15; // 1 => all slots, 2 => every second, 3 => every third, etc
    std::vector<long> pValues(ea.size(), 1);
    for (long i = 0; i < ea.size(); ++i) {
        if (i % interval == 0) {
            pValues[i] = RandomBits_long(bitSize);
#ifdef  DEBUG_PRINTOUT
            cout << "pValues[" << i << "]: " << pValues[i] << endl;
#endif
        }
    }

    // Encrypt the individual bits
    NTL::Vec<Ctxt> eValues, eIndices;

    resize(eValues, bitSize, Ctxt(secKey));
    for (long i = 0; i < bitSize; i++) {
        std::vector<long> t_pa = pValues;
        for (long &l : t_pa) {
            l = (l >> i) & 1;
        }
        ea.skEncrypt(eValues[i], secKey, t_pa);
        if (bootstrap) {
            // put them at a lower level
            eValues[i].modDownToLevel(5);
        }
    }

    if (verbose) {
        cout << "\n  bits-size " << bitSize << endl;
        CheckCtxt(eValues[0], "b4 internal addition");
    }

    // For the indices, find out how many bits we need:
    long bits = _ntl_g2logs(ea.size() / interval + 1);
    // Generate the fitting index at each position
    vector<long> pIndices(ea.size(), 1); //using 1 instead of 0 to make errors easier to spot
    int index = 0;
    for (int i = 0; i < ea.size(); ++i) {
        if (i % interval == 0) {
            pIndices[i] = index;
            ++index;
        }
    }

    // Encrypt the indices
    resize(eIndices, bits, Ctxt(secKey));
    for (long i = 0; i < bits; i++) {
        std::vector<long> t = pIndices;
        for (long &l : t) {
            l = (l >> i) & 1;
        }
        ea.skEncrypt(eIndices[i], secKey, t);
        if (bootstrap) {
            // put them at a lower level
            eIndices[i].modDownToLevel(5);
        }
    }

    // Test internal sort
    vector<long> v_slots;
    vector<long> i_slots;
    { // Wrappers
        CtPtrs_VecCt eev(eValues);
        CtPtrs_VecCt eei(eIndices);
        internalMin(eev, eei, interval, &unpackSlotEncoding);
        decryptBinaryNums(v_slots, eev, secKey, ea);
        decryptBinaryNums(i_slots, eei, secKey, ea);
    }
    if (verbose) CheckCtxt(eValues[lsize(eValues) - 1], "after internal addition");

    // All the values we care about should be at i % interval == 0
    // Grab just the values into a new vector to sort
    // Sorting rather than min because this was originally intended for sort, not min
    vector<std::pair<long, long>> sorted;
    for (int i = 0; i < ea.size(); ++i) {
        if (i % interval == 0) {
            sorted.emplace_back(std::make_pair(pValues[i], pIndices[i]));
        }
    }
    sort(sorted.begin(), sorted.end());

//#ifdef  DEBUG_PRINTOUT
//    cout << "sorted input: [";
//    for(auto &p : sorted) {
//      cout << "(" << p.first << "," << p.second << "), ";
//    }
//    cout << "]" << endl;
//#endif

    // Now go and compare them:

    if (v_slots[0] != (sorted[0].first)) {
        cout << "internal min error: min=" << v_slots[0]
             << " index=" << i_slots[0]
             << " (should be min=" << (sorted[0].first)
             << " index= " << (sorted[0].second)
             << ")\n";
        exit(0);
    } else if (verbose) {
        cout << "internal min succeeded";
    }

#ifdef DEBUG_PRINTOUT
    const Ctxt *minCtxt = nullptr;
    long minLvl = 1000;
    for (const Ctxt &c: eValues) {
        long lvl = c.findBaseLevel();
        if (lvl < minLvl) {
            minCtxt = &c;
            minLvl = lvl;
        }
    }
    decryptAndPrint((cout << " after internal min: "), *minCtxt, secKey, ea, 0);
    cout << endl;
#endif
}