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


#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <algorithm>
#include <time.h>

using namespace std;


FHEcontext context(1,2,3); // dummy context
FHEPubKey pubKey = FHESecKey(context); // dummy key

/** This class represents a bit. It carries a plaintext value, a ciphertext value and a symbolic name/equation **/
class Bit {
public:
	string name;
	bool plaintext;
	float  ciphertext; 
	int multiplications;
	


	Bit(string name, bool plaintext) {
		this->name = name;
		this->plaintext = plaintext;
		this->ciphertext = 0;
		this->multiplications = 0;
	}

	Bit(const Bit& b) {
		this->name = b.name;
		this->plaintext = b.plaintext;
		this->ciphertext = b.ciphertext;
		this->multiplications = b.multiplications;
	}

	// XOR
	Bit& operator+=(const Bit& rhs)
	{
		name = "TEST"; // "(" + name + "+" + rhs.name + ")";
		plaintext = plaintext ^ rhs.plaintext;
		ciphertext = ciphertext += rhs.ciphertext;
		multiplications = max(multiplications, rhs.multiplications);
		return *this;
	}

	// AND
	Bit& operator*=(const Bit& rhs) {
		name = "TEST"; // "(" + name + "." + rhs.name + ")";
		plaintext = plaintext && rhs.plaintext;
		ciphertext = ciphertext *= rhs.ciphertext;
		multiplications = max(multiplications, rhs.multiplications) + 1;
		return *this;
	}


};

// Pretty output from <<
std::ostream & operator<<(std::ostream & os, const Bit & foo)
{
	os << foo.name << "(" << foo.plaintext << ")";
	return os;
}

// Printing, both full as well as plaintext only for vector<Bit> and vector<*Bit>
string printvb(vector<Bit> &b) {
	stringstream ss;
	if (b.size() > 0) {
		ss << b[0];
	}
	for (size_t i = 1; i < b.size(); ++i) {
		ss << "," << b[i];
	}
	return ss.str();
}

string printvbp(vector<Bit> &b) {
	stringstream ss;
	for (size_t i = 0; i < b.size(); ++i) {
		ss << b[i].plaintext;
	}
	return ss.str();
}

string printvb(vector<Bit*> &b) {
	stringstream ss;
	for (size_t i = 0; i < b.size(); ++i) {
		if (b[i]) {
			ss << *b[i];
		}
		else {
			ss << "[NULL]";

		}
	}
	return ss.str();
}

string printvbp(vector<Bit*> &b) {
	stringstream ss;
	if (b.size() > 0 && b[0]) {
		ss << b[0]->plaintext;
	}
	else {
		ss << "[NULL]";

	}
	for (size_t i = 1; i < b.size(); ++i) {
		if (b[i]) {
			ss << b[i]->plaintext;
		}
		else {
			ss << "[NULL]";

		}
	}
	return ss.str();
}

unsigned long long gen_seed = 0;
/** Generate random binary numbers of length n. Name is set for Bit.name  **/
vector<Bit> gen(int n, string name)
{
	vector<Bit> x;
	if (gen_seed == 0) {
		gen_seed = time(NULL);
		srand(gen_seed);
	}
	for (int i = 0; i < n; i++) {
		stringstream ss;
		bool val = (rand() % 2) == 1;
		ss << name << "[" << i << "]";
		x.push_back(Bit(ss.str(), val));
	}
	return x;
}

/** Calculate two's-complement value of a binary number **/
long long val2(vector<Bit>& x)
{
	long long val = 0;
	int n = x.size();

	for (int i = 0; i < n; ++i) {
		val += x[i].plaintext * pow(2, i);
	}
	// Two's complement representation!
	if (x[n - 1].plaintext == 1)
	{
		val = val - pow(2, n);
	}
	return val;
}

/** Find the maximum multiplications in a vector<Bit> **/
int maxmult(vector<Bit> &x)
{
	int res = 0;
	for (size_t i = 0; i < x.size(); i++)
	{
		res = max(res, x[i].multiplications);
	}
	return res;
}

////////////////////  CL-ADDER HELPER CLASSES & FUNCTIONS  ///////////////////


/*
* This class represents an addend in the carry look ahead calculation
* It does so in a way that will minimize the multiplicative depth of the calculation
*/
//TODO: make vector<FTxt> an actual class/typedef?


/**
* This class represents a single component of a conjunction.
* The multiplicative depth indicates how many multiplications (and operations)
* have already been performed on the bits
**/
class FTxt {

public:
	Bit bit = Bit("[UNDEFINED]", 0);
	int multdepth;

	FTxt(Bit bit, int multdepth) {
		this->bit = bit;
		this->multdepth = multdepth;
	}

	bool operator < (const FTxt& other) const
	{
		return (multdepth < other.multdepth);
	}

};

// pretty <<
std::ostream & operator<<(std::ostream & os, const FTxt & foo)
{
	os << foo.bit.name << "(" << foo.bit.plaintext << ")";
	return os;
}

/**
* This routine is used to incrementally compute a divide-and-conquer conjunction
* of each of the addends in the carry calculations
* A "slot" contains a list of FTxts and should fullfill the condition that
* It is sorted (although we enforce this for now) w.r.t multdepth,
* and that for multdepths md1 md2 md3...mdn the condition
* 2^md1 < 2^m2 + 2^m3 + ....2^mn is fullfilled.
* I.e. the FTxts can be interpreted as a (potentially non-full) binary tree
* The whole thing is kind of hard to explain without a diagram ;)
**/

//TODO: Make this handle non-power-of-two-multdepths (e.g. inputs with MD already e.g. 3)
void updateslot(vector<FTxt>& slot, FTxt newtxt) {
	// Let's mak sure the slot is sorted
	sort(slot.begin(), slot.end());

	// and we can only add this correctly if newtxt is actually new:
	if (newtxt.multdepth != 0) {
		cout << "WARNING: CANNOT COMBINE!!" << endl;
		return;
	}

	// If we already have a 'lone' value, let's combine them:
	if (slot.back().multdepth == 0) {

		slot.back().bit *= newtxt.bit;
		slot.back().multdepth += 1;

		// Now we might be able to cascade this!
		int md = slot.back().multdepth;
		for (int i = slot.size() - 2; i >= 0; i--) {
			if (slot[i].multdepth == md) {
				//combine the last and current element!
				slot[i].bit *= slot.back().bit;
				slot[i].multdepth += 1;
				// the md we need to look for is also higher!
				md = slot[i].multdepth;
				//remove the last element
				slot.pop_back();
			}
		}

	}
	else { // if we have a 2,4,8,etc value-pack, we need to wait
		slot.push_back(newtxt);
	}
}


/**
* A single "slot" is a vector<Ftxt>.
* Therfore the list of slots is a vector<vector<Ftxt>>
* Since we calculate each c[i] incrementally, we need to ensure
* that no intermediate values that are re-used for c[i+1] are overriden
* We therefore look at each slot, duplicate one of the bits and then calculate
* the conjunction of the various slot-components "into" this duplicated bit
* The return value is the disjunction of all the slot conjunctions,
* i.e. we get the typical carry look ahead formula
* If the slots are 'valid' w.r.t updateslot then the return Bit will have
* multdepth only approx. log(N) larger than the inputs to the adder
* This allows us to calculate an add with a final maximum multdepth of only log(N) + 2
**/
Bit evalSlots(vector<vector<FTxt>> &elements) {

	// For each slot, calculate the internal AND
	//TODO:
	// also find the first slot where we had to create a new aggregation Bit
	// to later use that bit to aggregate the ORs into, too

	int s = elements.size();
	vector<Bit> slotRes;

	// Go through all slots
	for (int i = 0; i < s; ++i) {
		// cout << endl;

		// if a slot contains something then calculate its conjunction
		if (elements[i].size() > 0 && (elements[i][0].bit.name != "[UNDEFINED]")) {
			// cout << "calculating slot " << i << endl;
			// cout << "slot contains " << elements[i].size() << " parts" << endl;   
			vector<FTxt> slot = elements[i];
			// duplicate a Bit
			Bit b = slot[0].bit;
			// cout << "slot bit is " << b;
			//calculate the slot
			for (size_t j = 1; j < slot.size(); ++j) {
				// cout << b << "&&" << slot[j].bit;
				b *= slot[j].bit;
			}
			// cout << " = " << b.plaintext << endl;
			//push the RESULT
			slotRes.push_back(b);
		}

	}

	// Now that we have all slots, do the XOR
	if (slotRes.size() > 0) {
		for (size_t j = 1; j < slotRes.size(); ++j) {
			slotRes[0] += slotRes[j];
		}
	}
	else {
		cout << "SOMETHING WENT WRONG" << endl;
	}

	return slotRes[0];
}


/** Full Carry Lookahead Adder.
* Assumes x[0]=LSB, x[n-1]=MSB, ditto for y
* Result is written into x, with carry bit appended onto x
*  x[0] = LSB, x[n+1]=MSB, x[n]=Carry-out
**/
void adder(vector<Bit> &x, vector<Bit> &y, Bit &c0) {

	//TODO: PADDING
	// assumes both have same size
	int n = x.size();

	// calculate generate,propagate and non-carry sum
	vector<Bit> p;
	vector<Bit> g;
	for (int i = 0; i < n; ++i) {
		// cout << "taking " << x[i] << " and " << y[i] << ":" << endl;
		// duplicate for sum
		Bit b = x[i]; // now b is x_i
		x[i] += y[i]; // x[i] is now x_i ^ y_i
		y[i] *= b; //y[i] is now x_i && y_i 
		b = x[i]; // b is now x_i ^ y_i
				  // cout << "p = " << x[i] << endl;
				  // cout << "g = " << y[i] << endl;
				  // cout << "s = " << b << endl;
		p.push_back(x[i]);
		g.push_back(y[i]);
	}


	// Initialize Carries
	vector<Bit> c;
	c.push_back(c0);
	for (int i = 1; i <= n + 1; ++i) {
		stringstream ss;
		ss << "c[" << i << "]";
		c.push_back(Bit(ss.str(), 0));
	}

	// We store the 'reusable elements' of each 'slot' in here
	// see updateslot and evalSlots for more information
	vector<vector<FTxt> > elements(n + 1, vector<FTxt>());
	for (int i = 0; i<n + 1; ++i) {
		FTxt undef = FTxt(Bit("[UNDEFINED]", 0), 0);
		elements[i].push_back(undef);
	}

	// We start off with c[0]
	FTxt c0txt = FTxt(c[0], 1);
	elements[0][0] = c0txt;

	// For each of the output carries:
	for (int i = 1; i < n + 1; i++) {

		// Add g[i-1] to the sum
		FTxt gtxt = FTxt(g[i - 1], 0);
		elements[i][0] = gtxt;

		// Multiply all the other elements by p[i-1]
		for (int s = 1; s <= i; s++) {
			FTxt ptxt = FTxt(p[i - 1], 0);

			// updateslot stores each element as a vector of FTxt
			// where each FTxt has a power-of-two (or 0) multdepth
			// Together with evalSlots, this gives us log(N) multdepth
			// compared to naive incremental multiplications which would result in O(N) multdepth
			updateslot(elements[(i - s)], ptxt);

		}

		// Now that we have the final equation, we need to actually calculate c[i]
		c[i] = evalSlots(elements);

	}

	// Now that we have all carries, we update the sum
	// N.B. that we don't need to worry about carrying 
	// after all that's the entire point of the carry-look-ahead calculation
	for (int i = 0; i < n; ++i) {
		x[i] += c[i];
	}
	// carry out
	x.push_back(c[n]);
}

/**
* Calculate a-b
*/
void subtract(vector<Bit> &a, vector<Bit> &b)
{
	// first, let's invert b
	Bit onebit = Bit("ONE", true);
	for (size_t i = 0; i < b.size(); i++)
	{
		b[i] += onebit; //XOR with 1 is negation
	}

	//cout << "inv(b): " << printvbp(b) << endl;

	// The "+1" for two's complement comes from the carry in
	adder(a, b, onebit);

	//cout << "add res:" << printvbp(a) << endl;

	a.pop_back();
	// but ignore the carry/out:
	//a[a.size()-1] = Bit("ZERO", 0, 0);
}

/**
* Custom multiplication system optimized for squaring
* !!!! DOES NOT SUPPORT TWO'S COMPLEMENT !!!!
*  use signextend(x); square(x); reduce(x); as a work-around
*  TODO: Make this work natively and efficiently with two's complement
*  Assumes x[0]=LSB, x[n-1]=MSB
* returns x = x*x with x[0]=LSB, x[(2*n)-1]=MSB
* This is not guaranteed to work for non-power-of-two sizes
**/
void square(vector<Bit> &x) {
	int n = x.size();
	//cout << "n = " << n << endl;

	// Expanding x by two to the right makes the last pyramid step use the same code as the previous longest
	Bit zerobit = Bit("ZERO", 0);
	x.push_back(zerobit);
	x.push_back(zerobit);


	/* We use standard "long multiplication", however we use two optimizations:
	* While this isn't really a Wallace Tree multiplier, the ideas of channels/weights
	* from a Wallace Tree multiplier might be helpful to understand how this squaring algorithm works
	*
	* (1) When squaring, every sub-term x[i]*x[j] for i!=j will appear twice in the same channel
	* e.g. the 5th bit of the result (ignoring carries) will be x[0]*x[4] + x[1]*x[3] + x[3]*x[1] + x[0]*x[4]
	* Instead of calculating this,we can use the symmetry to see that this is just 2 * (x[0]*x[4] + x[1]*x[3])
	* and multiplication by two just means shifting to the next higher channel/bit, i.e. instead of adding four terms to bit 5,
	* we add only the two terms  x[0]*x[4] + x[1]*x[3] to bit 6
	* N.B. terms of the form x[i]*x[i] appear only once
	*
	* (2) Instead of naively adding the partial results from shortest to longest (like one would do if doing long multiplication by hand)
	* We re-arrange the results according to symmetry and into a pyramid. We also delay the addition of padding zeros until it is necessary
	* Instead of adding from the top to bottom:
	* ---xxxxx
	* --xxxxx0
	* -xxxxx00
	* xxxx0000
	*
	* We first use symmetry: (shift over and de-duplicate)
	* -xxxxxx-x
	* -x-xx-x--
	* ---x-----
	* and then add from the bottom up (less visible with 4/5-bit example, but generally we will get a "triangle shape" with the top pointing 'down')
	* Probably needs a real diagram to explain more clearly
	*/



	// We have 2*n - 1 bits but since we added two bits of zero-padding to the right, we can think of it as 2*n + 1
	// This means we can think of it as  n + 1 + n bits
	// The center 1 bit is the highest point of the pyramid
	// We refer to this center as the "middle" and the n bits to either side as "left" and "right"
	// The pyramid's structure means that each step "down" the pyramid adds two bits on each side
	int steps = static_cast<int>(ceil(n / 2.f));

	// We work with full-width vectors but leave the unneeded elements uninitialized (NULL)
	// "pre" is the result of the previous (higher) addition 
	vector<Bit*> pre(2 * n + 1);

	// At the beginning, we initalize pre with the lone term at the top of the 'pyramid'
	// The center of the pyramid is at index n (i.e. the n+1'th bit) and contains x[n/2]*x[n/2];
	Bit *t = new Bit(x[n / 2]);
	pre[n] = t;

	for (int k = 1; k <= steps; k++) {
		//cout << "----------- step: " << k << " -----------" << endl;
		vector<Bit*> cur(2 * n + 1);

		// Now collect all the values on the current step
		// midle values, useful for left/right calc
		int middle_value_r = n / 2 - k;
		int middle_value_l = n - (steps - k) - 1;

		// left of the middle we have:
		//cout << "left: ";
		// one factor is always x[middle_value_r]
		// the second factor is always (cur-index - factor_one) - 1
		// except when cur-index %2 = 0 because then it's just x[middle_value_r]
		for (int i = (2 * k); i >= 1; i--) {
			// current index
			int cur_index = n - i;
			if (i == (2 * k) - 1) {
				//cout << "ZERO,";
				cur[cur_index] = new Bit(zerobit);
			}
			else if (cur_index == 2 * (middle_value_r)) {
				//cout << "x[" << middle_value_r << "],";
				cur[cur_index] = new Bit(x[middle_value_r]);
			}
			else {
				//cout << "x[" << middle_value_r << "]*x[" << (cur_index - middle_value_r) - 1 << "],";
				Bit* b = new Bit(x[middle_value_r]);
				*b *= x[(cur_index - middle_value_r) - 1];
				cur[cur_index] = b;
			}
		}
		//cout << endl;


		// on the middle column, the values are
		//cout << "middle: x[" << middle_value_l << "]*x[" << middle_value_r << "]" << endl;
		Bit *b = new Bit(x[middle_value_l]);
		*b *= x[middle_value_r];
		cur[n] = b;

		// right of the middle we have:
		//cout << "right:";
		// one factor is always x[middle_value_l]
		// the second factor is always (cur-index - factor_one) - 1
		// except when cur-index %2 = 0 because then it's just x[middle_value_l]
		for (int i = 1; i < (2 * k) + 1; ++i) {
			//current index
			int cur_index = n + i;
			if (i == (2 * k) - 1) {
				//cout << "ZERO,";
				cur[cur_index] = new Bit(zerobit);
			}
			else if (cur_index == 2 * (middle_value_l + 1)) {
				//cout << "x[" << middle_value_l + 1 << "],";
				cur[cur_index] = new Bit(x[middle_value_l + 1]);
			}
			else {
				//cout << "x[" << (cur_index - middle_value_l) - 1 << "]*x[" << middle_value_l << "],";
				Bit *b = new Bit(x[(cur_index - middle_value_l) - 1]);
				*b *= x[middle_value_l];
				cur[cur_index] = b;
			}
		}
		//cout << endl;


		// Now that we have prepared cur, we need to add it to pre
		// But first we need to change from vector<Bit*>
		// i.e. vectors like [NULL] [NULL] Bit* Bit* Bit* [NULL] [NULL]
		// to a right-sized vector<Bit>
		// The current 'right' size is given by 2*k + 1 + 2*k, centered on index n
		vector<Bit> temp_pre;
		vector<Bit> temp_cur;
		for (int i = n - 2 * k; i <= n + 2 * k; ++i) {
			if (pre[i]) {
				temp_pre.push_back(*pre[i]);
			}
			else {
				temp_pre.push_back(zerobit);
			}

			if (cur[i]) {
				temp_cur.push_back(*cur[i]);
			}
			else {
				temp_cur.push_back(zerobit);
			}
		}
		//cout << "pre: " << printvbp(pre) << endl;
		//cout << "temp_pre: " << printvbp(temp_pre) << endl;

		// cout <<"cur: " << printvb(cur) << endl;
		//cout << "temp_cur: " << printvbp(temp_cur) << endl;

		// Now we can finally add them
		adder(temp_pre, temp_cur, zerobit);

		//cout << "added them" << endl;

		//cout << "new pre:  " << printvbp(temp_pre) << endl;

		// And push the result back to the real previous
		int j = 0;
		for (int i = n - 2 * k; i <= n + 2 * k; ++i) {
			pre[i] = new Bit(temp_pre[j++]);
		}



		// cout << "a+=b" << printvbp(a) << endl;
		// //And now we need to do the whole thing backwards:
		// for(int i=0; i < a.size(); ++i) {
		//   pre[(n-k)+i] = new Bit(a[i]);
		// }

		// cout << "new pre:  " << printvbp(pre) << endl;


	}

	//cout << "----------- output -----------" << endl;
	//cout << "x*x: ";
	x.clear();
	for (int i = 0; i < 2 * n; i++) {
		//cout << pre[i]->plaintext << ",";
		x.push_back(*pre[i]);
	}
	//cout << endl;

}

/** Helper to use squaring with two's complement
* !!! WARNING!!! HIGHLY INEFFECICIENT !!! **/
void square_signed(vector<Bit> &x)
{
	int n = x.size();
	for (int i = n; i < 2 * n; i++)
	{
		x.push_back(x[n - 1]);
	}

	square(x);

	for (int i = 0; i < 2 * n; i++)
	{
		x.pop_back();
	}
}

void testAdder(int n) {
	cout << "Testing Adder:" << endl;
	cout << "n: " << n << endl;

	vector<Bit> x;
	vector<Bit> y;
	Bit c0 = Bit("c[0]", 0);

	// Generate x (and calculate decimal value)
	x = gen(n, "x");
	long long xval = val2(x);
	cout << "x: " << printvbp(x) << " (" << xval << ")" << endl;

	// Generate y (and calculate decimal value)
	y = gen(n, "y");
	long long yval = val2(y);
	cout << "y: " << printvbp(y) << " (" << yval << ")" << endl;

	// Carrry out the addition
	adder(x, y, c0);

	// Test the result
	cout << "result: ";
	long long rval = val2(x);
	cout << "r: " << printvbp(x) << " (" << rval << ")" << endl;

	if (rval == xval + yval) {
		cout << "pass." << endl;
	}
	else {
		cout << "FAILED!!! Should be " << xval + yval << " but was " << rval << endl;
	}
}

void testSquare(int n) {

	cout << "Testing Squaring:" << endl;
	cout << "n: " << n << endl;

	// Generate x (and calculate value)	
	vector<Bit> x = gen(n, "x");
	long long xval = val2(x);
	cout << "x: " << printvbp(x) << " (" << xval << ")" << endl;

	// Square it
	square(x);

	// Display and test the result
	long long rval = val2(x);
	cout << "r: " << printvbp(x) << " (" << rval << ")" << endl;
	if (rval == xval * xval) {
		cout << "pass." << endl;
	}
	else {
		cout << "FAILED!!! Should be " << xval * xval << " but was " << rval << endl;
	}
}

void testSubtract(int n)
{
	cout << "Testing Subtractor:" << endl;
	cout << "n: " << n << endl;

	// Generate x:
	vector<Bit> x = gen(n, "x");
	long long xval = val2(x);
	cout << "x: " << printvbp(x) << " (" << xval << ")" << endl;

	// Generate y
	vector<Bit> y = gen(n, "y");
	long long yval = val2(y);
	cout << "y: " << printvbp(y) << " (" << yval << ")" << endl;

	// Carrry out the addition
	subtract(x, y);

	// Test the result	
	long long rval = val2(x);
	cout << "r: " << printvbp(x) << " (" << rval << ")" << endl;

	if (rval == xval - yval) {
		cout << "pass." << endl;
	}
	else if (xval - yval < -(pow(2, n - 1)) || xval - yval > pow(2, n - 1) - 1) {
		cout << "OVER/UNDERFLOW" << endl;
	}
	else {
		cout << "FAILED!!! Should be " << xval - yval << " but was " << rval << endl;
	}
}

void testChain()
{
	// We start with 15bit numbers
	int n = 13;

	// Generate four values x1,x2 and y1,y2
	vector<Bit> x1 = gen(n, "x1");
	long long x1val = val2(x1);
	cout << "x1: " << printvbp(x1) << " (" << x1val << ")" << endl;

	vector<Bit> y1 = gen(n, "y1");
	long long y1val = val2(y1);
	cout << "y1: " << printvbp(y1) << " (" << y1val << ")" << endl;

	vector<Bit> x2 = gen(n, "x2");
	long long x2val = val2(x2);
	cout << "x2: " << printvbp(x2) << " (" << x2val << ")" << endl;

	vector<Bit> y2 = gen(n, "y2");
	long long y2val = val2(y2);
	cout << "y2: " << printvbp(y2) << " (" << y2val << ")" << endl;

	// Start the distance calculation by doing x1-x2, y1-y2
	subtract(x1, x2);

	// Make sure the results are correct
	bool overflow = false;
	bool error = false;

	// Test dx
	long long dxval = val2(x1);
	cout << "dx: " << printvbp(x1) << " (" << dxval << ") ";

	if (dxval = x1val - x2val) {
		cout << "pass";
	}
	else if (x1val - x2val < -(pow(2, n - 1)) || x1val - x2val > pow(2, n - 1) - 1)
	{
		overflow = true;
		cout << "OVERFLOW!!!";
	}
	else
	{
		error = true;
		cout << "FAILED!! Should be " << x1val - x2val << " but was " << dxval;
	}
	cout << endl;

	// Test dy
	subtract(y1, y2);
	long long dyval = val2(y1);
	cout << "dy: " << printvbp(y1) << " (" << dyval << ") ";

	if (dyval = y1val - y2val) {
		cout << "pass";
	}
	else if (y1val - y2val < -(pow(2, n - 1)) || y1val - y2val > pow(2, n - 1) - 1)
	{
		overflow = true;
		cout << "OVERFLOW!!!";
	}
	else
	{
		error = true;
		cout << "FAILED!! Should be " << y1val - y2val << " but was " << dyval;
	}
	cout << endl;

	// Now square dx and dy	
	square_signed(x1);
	long long dx2val = val2(x1);
	cout << "dx2:" << printvbp(x1) << " (" << dx2val << ") ";
	if (dx2val == dxval * dxval) {
		cout << "pass";
	}
	else if (dxval * dxval < -(pow(2, n)) || dxval * dxval  > pow(2, n) - 1)
	{
		overflow = true;
		cout << "OVERFLOW!!!";
	}
	else {
		cout << "FAILED!! Should be " << dxval*dxval << " but was " << dx2val;
	}
	cout << endl;

	square_signed(y1);
	long long dy2val = val2(y1);
	cout << "dy2:" << printvbp(y1) << " (" << dy2val << ") ";
	if (dy2val == dyval * dyval) {
		cout << "pass";
	}
	else if (dyval * dyval < -(pow(2, n)) || dyval * dyval  > pow(2, n) - 1)
	{
		overflow = true;
		cout << "OVERFLOW!!!";
	}
	else {
		cout << "FAILED!! Should be " << dyval*dyval << " but was " << dy2val;
	}
	cout << endl;

	// And add the results
	Bit zerobit = Bit("c[0]", false); // carry in
	adder(x1, y1, zerobit);
	long long d2val = val2(x1);
	cout << "d2: " << printvbp(x1) << " (" << d2val << ") ";
	if (d2val == dy2val + dx2val) {
		cout << "pass";
	}
	else if (dy2val + dx2val < -(pow(2, n)) || dy2val + dx2val > pow(2, n) - 1)
	{
		overflow = true;
		cout << "OVERFLOW!!!";
	}
	else {
		error = true;
		cout << "FAILED!! Should be " << dy2val + dx2val << " but was " << d2val;
	}
	cout << endl;

	// Find out the multiplication depth:
	cout << "multiplication depth: " << maxmult(x1) << endl;
}

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

  context = FHEcontext(m, p, r);
  buildModChain(context, /*L=*/levels);
  // cout << context << endl;
  // context.zMStar.printout();
  // cout << endl;

  cout << "Generating keys and key-switching matrices... " << std::flush;
  FHESecKey* secretKey = new FHESecKey(context);
  secretKey->GenSecKey(/*w=*/64);// A Hamming-weight-w secret key
  addFrbMatrices(*secretKey); // compute key-switching matrices that we need
  add1DMatrices(*secretKey); // compute key-switching matrices that we need
  FHEPubKey publicKey = *secretKey;  

  setTimersOff();
  printAllTimers();
  cout << "done\n";
  resetAllTimers();

  EncryptedArray ea = *(context.ea);
  ea.buildLinPolyMat(false);
  
  Ctxt ctxt(publicKey);
  NewPlaintextArray ptxt(ea);
  random(ea, ptxt);
  // // ea.encrypt(ctx:wqt, publicKey, ptxt);
  ea.skEncrypt(ctxt, *secretKey, ptxt);


  cout << "Extracting " << nb_coeffs << " coefficients...";
  vector<Ctxt> coeffs;
  extractCoeffs(ea, coeffs, ctxt, nb_coeffs);
  cout << "done\n";

  vector<ZZX> ptxtDec;
  ea.decrypt(ctxt, *secretKey, ptxtDec);

  for (long i=0; i<(long)coeffs.size(); i++) {
     if (!coeffs[i].isCorrect()) {
       cerr << " potential decryption error for "<<i<<"th coeffs " << endl;
       CheckCtxt(coeffs[i], "");
       exit(0);
     }
     vector<ZZX> pCoeffs;
     ea.decrypt(coeffs[i], *secretKey, pCoeffs);

     assert(pCoeffs.size() == ptxtDec.size());

     for (int j = 0; j < pCoeffs.size(); ++j) {
       if (coeff(pCoeffs[j], 0) != coeff(ptxtDec[j], i)) {
         cerr << "error: extracted coefficient " << i << " from " 
           "slot " << j << " is " << coeff(pCoeffs[j], 0) << " instead of " << 
           coeff(ptxtDec[j], i) << endl;
         exit(0);
     }
   }

  }  
  cerr << "Extracted coefficient successfully verified!\n";
}




