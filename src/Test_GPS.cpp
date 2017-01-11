/* This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 */

/**
 * Test_extractCoeffs.cpp - extract polynomial coefficients.
 *  For an encryption of a polynomial extract its coefficients into 
 *  separate encryptions. 
 *  For example from Enc(a+b.X+c.X^2+...) obtain Enc(a), Enc(b), Enc(c),...
 */


#include "FHE.h"
#include "timing.h"
#include "EncryptedArray.h"

/**
 * @brief Extract coefficients from ciphertext polynomial

 * @param coeffs extracted coefficients
 * @param ctxt ciphertext
 * @param n extract "n" lowest degree coefficients
 */
void extractCoeffs(EncryptedArray& ea, vector<Ctxt>& coeffs, Ctxt& ctxt, long n) {
  long d = ea.getDegree();
  if (d < n) n = d;

  coeffs.clear();

  vector<Ctxt> conj;  
  for (int coeff = 0; coeff < n; ++coeff) {
    vector<ZZX> LM(d);
    LM[coeff] = ZZX(0, 1);

    // "building" the linearized-polynomial coefficients
    vector<ZZX> C(d);
    ea.buildLinPolyCoeffs(C, LM);

    coeffs.push_back(ctxt);
    applyLinPoly1(ea, coeffs[coeff], C, conj);
  }
}


int main(int argc, char *argv[]) 
{
  ArgMapping amap;

/*
 long m=0, p=2, r=1; // Native plaintext space
                        // Computations will be 'modulo p'
    long L=16;          // Levels
    long c=3;           // Columns in key switching matrix
    long w=64;          // Hamming weight of secret key
    long d=0;
    long security = 128;
    ZZX G;
    
    
    m = FindM(security,L,c,p, d, 0, 0);
*/
  long security = 80; // security level
  long p=2;
  long r=1;
  long c=2;           // Columns in key switching matrix
  long levels=32;
  long nb_coeffs=5;
  long d=0; // is this the same as r? No
  long s = 32; // at least 32 slots because of return value!
  long m=FindM(security,levels,c,p, d, s, 0);
  
  
  amap.arg("p", p, "plaintext base");
  amap.arg("r", r,  "lifting");
  amap.arg("L", levels,  "levels");
  amap.arg("n", nb_coeffs,  "nb coefficients to extract");
  amap.arg("m", m, "use specified value as modulus");
  amap.parse(argc, argv);

  cout << "\n\n******** generate parameters"
       << " m=" << m 
       << ", p=" << p
       << ", r=" << r
       << ", n=" << nb_coeffs
       << endl;

  setTimersOn();

  FHEcontext* context = new FHEcontext(m, p, r);
  buildModChain(*context, /*L=*/levels);
  // cout << context << endl;
  // context.zMStar.printout();
  // cout << endl;

  cout << "Generating keys and key-switching matrices... " << std::flush;
  FHESecKey* secretKey = new FHESecKey(*context);
  secretKey->GenSecKey(/*w=*/64);// A Hamming-weight-w secret key
  addFrbMatrices(*secretKey); // compute key-switching matrices that we need
  add1DMatrices(*secretKey); // compute key-switching matrices that we need
  const FHEPubKey* publicKey = secretKey;  

  setTimersOff();
  printAllTimers();
  cout << "done\n";
  resetAllTimers();

  // EncryptedArray ea = *(context.ea);
  // ea.buildLinPolyMat(false);

  // Ctxt ctxt(publicKey);
  // NewPlaintextArray ptxt(ea);
  // random(ea, ptxt);
  // // ea.encrypt(ctxt, publicKey, ptxt);
  // ea.skEncrypt(ctxt, secretKey, ptxt);


  // cout << "Extracting " << nb_coeffs << " coefficients...";
  // vector<Ctxt> coeffs;
  // extractCoeffs(ea, coeffs, ctxt, nb_coeffs);
  // cout << "done\n";

  // vector<ZZX> ptxtDec;
  // ea.decrypt(ctxt, secretKey, ptxtDec);

  // for (long i=0; i<(long)coeffs.size(); i++) {
  //   if (!coeffs[i].isCorrect()) {
  //     cerr << " potential decryption error for "<<i<<"th coeffs " << endl;
  //     CheckCtxt(coeffs[i], "");
  //     exit(0);
  //   }
  //   vector<ZZX> pCoeffs;
  //   ea.decrypt(coeffs[i], secretKey, pCoeffs);

  //   assert(pCoeffs.size() == ptxtDec.size());

  //   for (int j = 0; j < pCoeffs.size(); ++j) {
  //     if (coeff(pCoeffs[j], 0) != coeff(ptxtDec[j], i)) {
  //       cerr << "error: extracted coefficient " << i << " from " 
  //         "slot " << j << " is " << coeff(pCoeffs[j], 0) << " instead of " << 
  //         coeff(ptxtDec[j], i) << endl;
  //       exit(0);
  //     }
  //   }

  // }  
  // cerr << "Extracted coefficient successfully verified!\n";
}




