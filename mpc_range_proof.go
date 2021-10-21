package mbp

import (
	"crypto/rand"
	"crypto/sha256"
	"fmt"
	"math/big"
)

// MPCRangeProof is a struct of secure multi-party computation range proof
type MPCRangeProof struct {
	Comms []ECPoint
	A     ECPoint
	S     ECPoint
	T1    ECPoint
	T2    ECPoint
	Tau   *big.Int
	Th    *big.Int
	Mu    *big.Int
	IPP   InnerProdArg

	// challenges
	Cy *big.Int
	Cz *big.Int
	Cx *big.Int
}

// PrivateParams is the private params of Prover
type PrivateParams struct {
	Id    int
	V     *big.Int
	AL    []*big.Int
	AR    []*big.Int
	SL    []*big.Int
	SR    []*big.Int
	Gamma *big.Int
	Alpha *big.Int
	Rho   *big.Int
	Tt0    *big.Int
	Tt1    *big.Int
	Tt2    *big.Int
	Tau1  *big.Int
	Tau2  *big.Int
}

type InitParams struct {
	//EC CryptoParams
	N  int
	M  int
}

type ASCommitment struct {
	Comm ECPoint
	A    ECPoint
	S    ECPoint
}

type T1T2Commitment struct {
	T1 ECPoint
	T2 ECPoint
}

type OtherShare struct {
	Left  []*big.Int
	Right []*big.Int
	That  *big.Int
	Taux  *big.Int
	Mu    *big.Int
}

func AandS(v *big.Int, id, m int, prip *PrivateParams, EC CryptoParams) ASCommitment {

	AS := ASCommitment{}
	fmt.Printf("v: %v\n", v)
	bitsPerValue := EC.V / m //

	if v.Cmp(big.NewInt(0)) == -1 {
		panic("Value is below range! Not proving")
	}

	if v.Cmp(new(big.Int).Exp(big.NewInt(2), big.NewInt(int64(bitsPerValue)), EC.N)) == 1 {
		panic("Value is above range! Not proving.")
	}
	prip.Id = id
	prip.V = v
	gamma, err := rand.Int(rand.Reader, EC.N)
	prip.Gamma = gamma
	fmt.Printf("gamma: %v\n", gamma)
	check(err)
	comm := EC.G.Mult(v, EC).Add(EC.H.Mult(gamma, EC), EC)
	AS.Comm = comm

	aL := reverse(StrToBigIntArray(PadLeft(fmt.Sprintf("%b", v), "0", bitsPerValue)))
	prip.AL = aL

	aR := VectorAddScalar(aL, big.NewInt(-1), EC)
	prip.AR = aR

	alpha, err := rand.Int(rand.Reader, EC.N)
	check(err)
	prip.Alpha = alpha

	// 设置cryptoparams.go中  v = n * m
	BPG := EC.BPG[id*bitsPerValue : (id+1)*bitsPerValue]
	BPH := EC.BPH[id*bitsPerValue : (id+1)*bitsPerValue]

	A := TwoVectorPCommitWithGens(BPG, BPH, aL, aR, EC).Add(EC.H.Mult(alpha, EC), EC)
	AS.A = A

	sL := RandVector(bitsPerValue, EC)
	sR := RandVector(bitsPerValue, EC)
	prip.SL = sL
	prip.SR = sR

	rho, err := rand.Int(rand.Reader, EC.N)
	check(err)
	prip.Rho = rho

	S := TwoVectorPCommitWithGens(BPG, BPH, sL, sR, EC).Add(EC.H.Mult(rho, EC), EC)
	AS.S = S
	return AS
}

func Fait_y_z(A, S []ECPoint, mpcrp *MPCRangeProof, EC CryptoParams) (*big.Int, *big.Int) {

	countA := EC.Zero()
	countS := EC.Zero()

	for i := 0; i < len(A); i++ {
		// 是代码中定义的加  代码定义
		countA = countA.Add(A[i], EC)
		countS = countS.Add(S[i], EC)
	}

	mpcrp.A = countA
	mpcrp.S = countS

	chal1s256 := sha256.Sum256([]byte(countA.X.String() + countA.Y.String()))
	cy := new(big.Int).SetBytes(chal1s256[:])
	mpcrp.Cy = cy

	chal2s256 := sha256.Sum256([]byte(countS.X.String() + countS.Y.String()))
	cz := new(big.Int).SetBytes(chal2s256[:])
	mpcrp.Cz = cz

	return cy, cz
}

/*
DeltaMPC is a helper function that is used in the range proof

\DeltaMPC(y, z) = (z-z^2)<1^n, y^n> - z^3 * z^j * <1^n, 2^n>
*/

func DeltaMPC(y []*big.Int, z *big.Int, id, m int, EC CryptoParams) *big.Int {
	result := big.NewInt(0)

	// (z-z^2)<1^n, y^n>
	z2 := new(big.Int).Mod(new(big.Int).Mul(z, z), EC.N)
	t1 := new(big.Int).Mod(new(big.Int).Sub(z, z2), EC.N)
	t2 := new(big.Int).Mod(new(big.Int).Mul(t1, VectorSum(y, EC)), EC.N)

	// z^(3+j)<1^n, 2^n>
	z3j := new(big.Int).Exp(z, big.NewInt(3+int64(id)), EC.N)
	po2sum := new(big.Int).Sub(new(big.Int).Exp(big.NewInt(2), big.NewInt(int64(EC.V/m)), EC.N), big.NewInt(1))
	t3 := new(big.Int).Mod(new(big.Int).Mul(z3j, po2sum), EC.N)

	result = new(big.Int).Mod(new(big.Int).Sub(t2, t3), EC.N)

	return result
}

func T1andT2(v *big.Int, id, m int, cy, cz *big.Int, prip *PrivateParams, EC CryptoParams) T1T2Commitment {

	t1t2 := T1T2Commitment{}
	// aL  aR sL sR
	aL := prip.AL
	aR := prip.AR
	sL := prip.SL
	sR := prip.SR

	bitsPerValue := EC.V / m

	// PowerOfTwos
	PowerOfTwos := PowerVector(bitsPerValue, big.NewInt(2), EC)
	PowerOfCY := PowerVector(EC.V, cy, EC) // EC.V = n * m

	zPowersTimesTwoVec := make([]*big.Int, EC.V) //
	for j := 0; j < m; j++ {
		zp := new(big.Int).Exp(cz, big.NewInt(2+int64(j)), EC.N)
		for i := 0; i < bitsPerValue; i++ {
			zPowersTimesTwoVec[j*bitsPerValue+i] = new(big.Int).Mod(new(big.Int).Mul(PowerOfTwos[i], zp), EC.N)
		}
	}

	yn := PowerOfCY[id*bitsPerValue : (id+1)*bitsPerValue]
	z2j2n := zPowersTimesTwoVec[id*bitsPerValue : (id+1)*bitsPerValue]

	l0 := VectorAddScalar(aL, new(big.Int).Neg(cz), EC)
	l1 := sL
	r0 := VectorAdd(
		VectorHadamard(
			yn,
			VectorAddScalar(aR, cz, EC), EC),
		z2j2n, EC)
	r1 := VectorHadamard(sR, yn, EC)

	//calculate t0
	z2 := new(big.Int).Mod(new(big.Int).Mul(cz, cz), EC.N)
	PowerOfCZ := PowerVector(m, cz, EC)

	vz2 := new(big.Int).Mul(PowerOfCZ[id], new(big.Int).Mul(v, z2))
	vz2 = new(big.Int).Mod(vz2, EC.N)

	t0 := new(big.Int).Mod(new(big.Int).Add(vz2, DeltaMPC(yn, cz, id, m, EC)), EC.N)
	t1 := new(big.Int).Mod(new(big.Int).Add(InnerProduct(l1, r0, EC), InnerProduct(l0, r1, EC)), EC.N)
	t2 := InnerProduct(l1, r1, EC)

	prip.Tt0 = t0
	prip.Tt1 = t1
	prip.Tt2 = t2

	// given the t_i values, we can generate commitments to them
	tau1, err := rand.Int(rand.Reader, EC.N)
	check(err)
	tau2, err := rand.Int(rand.Reader, EC.N)
	check(err)
	prip.Tau1 = tau1
	prip.Tau2 = tau2

	T1 := EC.G.Mult(t1, EC).Add(EC.H.Mult(tau1, EC), EC) //commitment to t1
	T2 := EC.G.Mult(t2, EC).Add(EC.H.Mult(tau2, EC), EC) //commitment to t2
	t1t2.T1 = T1
	t1t2.T2 = T2
	return t1t2
}

func Fait_x(T1, T2 []ECPoint, mpcrp *MPCRangeProof, EC CryptoParams) *big.Int {
	countT1 := EC.Zero()
	countT2 := EC.Zero()
	for i := 0; i < len(T1); i++ {
		countT1 = countT1.Add(T1[i], EC)
		countT2 = countT2.Add(T2[i], EC)
	}

	mpcrp.T1 = countT1
	mpcrp.T2 = countT2

	chal3s256 := sha256.Sum256([]byte(countT1.X.String() + countT1.Y.String() + countT2.X.String() + countT2.Y.String()))
	cx := new(big.Int).SetBytes(chal3s256[:])

	mpcrp.Cx = cx
	return cx
}

func ProFinal(v *big.Int, id, m int, cy, cz, cx *big.Int, prip *PrivateParams, EC CryptoParams) OtherShare {
	share := OtherShare{}
	// aL  aR  sL sR
	aL := prip.AL
	aR := prip.AR
	sL := prip.SL
	sR := prip.SR

	// PowerOfCY  PowerOfTwos  zPowersTimesTwoVec
	bitsPerValue := EC.V / m
	PowerOfCY := PowerVector(EC.V, cy, EC)
	PowerOfTwos := PowerVector(bitsPerValue, big.NewInt(2), EC)
	zPowersTimesTwoVec := make([]*big.Int, EC.V) //
	for j := 0; j < m; j++ {
		zp := new(big.Int).Exp(cz, big.NewInt(2+int64(j)), EC.N)
		for i := 0; i < bitsPerValue; i++ {
			zPowersTimesTwoVec[j*bitsPerValue+i] = new(big.Int).Mod(new(big.Int).Mul(PowerOfTwos[i], zp), EC.N)
		}
	}

	yn := PowerOfCY[id*bitsPerValue : (id+1)*bitsPerValue]
	z2j2n := zPowersTimesTwoVec[id*bitsPerValue : (id+1)*bitsPerValue]

	left := CalculateLMRP(aL, sL, cz, cx, EC)
	right := CalculateRMRP(aR, sR, yn, z2j2n, cz, cx, EC)
	share.Left = left
	share.Right = right

	// t0 t1 t2
	t0 := prip.Tt0
	t1 := prip.Tt1
	t2 := prip.Tt2

	thatPrime := new(big.Int).Mod( // t0 + t1*x + t2*x^2
		new(big.Int).Add(t0, new(big.Int).Add(new(big.Int).Mul(t1, cx), new(big.Int).Mul(new(big.Int).Mul(cx, cx), t2))), EC.N)

	that := InnerProduct(left, right, EC) // NOTE: BP Java implementation calculates this from the t_i

	// thatPrime and that should be equal
	if thatPrime.Cmp(that) != 0 {
		fmt.Println("Proving -- Uh oh! Two diff ways to compute same value not working")
		fmt.Printf("\tthatPrime = %s\n", thatPrime.String())
		fmt.Printf("\tthat = %s \n", that.String())
	}
	share.That = that

	// tau1, tau2, gamma rho
	tau1 := prip.Tau1
	tau2 := prip.Tau2
	gamma := prip.Gamma
	rho := prip.Rho
	alpha := prip.Alpha
	fmt.Printf("gamma: %v\n", gamma)
	taux1 := new(big.Int).Mod(new(big.Int).Mul(tau2, new(big.Int).Mul(cx, cx)), EC.N)
	taux2 := new(big.Int).Mod(new(big.Int).Mul(tau1, cx), EC.N)
	z2j := new(big.Int).Exp(cz, big.NewInt(2+int64(id)), EC.N)
	tmp1 := new(big.Int).Mul(gamma, z2j)
	taux := new(big.Int).Mod(new(big.Int).Add(taux1, new(big.Int).Add(taux2, tmp1)), EC.N)
	mu := new(big.Int).Mod(new(big.Int).Add(alpha, new(big.Int).Mul(rho, cx)), EC.N)
	share.Taux = taux
	share.Mu = mu
	return share
}

func DealerFinal(left, right []*big.Int, tx, rx, mu []*big.Int, m int, mpcrp *MPCRangeProof, cy *big.Int, EC CryptoParams) {

	countThat := big.NewInt(0)
	countTaux := big.NewInt(0)
	countMu := big.NewInt(0)

	countLeft := left
	countRight := right

	bitsPerValue := EC.V / m

	for j := 0; j < len(tx); j++ {
		countThat = new(big.Int).Add(countThat, tx[j])
		countTaux = new(big.Int).Add(countTaux, rx[j])
		countMu = new(big.Int).Add(countMu, mu[j])

	}

	mpcrp.Tau = countTaux
	mpcrp.Th = countThat
	mpcrp.Mu = countMu

	HPrime := make([]ECPoint, len(EC.BPH))

	PowerOfCY := PowerVector(EC.V, cy, EC)
	for j := 0; j < m; j++ {
		for i := 0; i < bitsPerValue; i++ {
			HPrime[j*bitsPerValue+i] = EC.BPH[j*bitsPerValue+i].Mult(new(big.Int).ModInverse(PowerOfCY[j*bitsPerValue+i], EC.N), EC)
		}
	}

	P := TwoVectorPCommitWithGens(EC.BPG, HPrime, countLeft, countRight, EC)
	that := InnerProduct(countLeft, countRight, EC)
	IPP := InnerProductProve(countLeft, countRight, that, P, EC.U, EC.BPG, HPrime, EC)
	mpcrp.IPP = IPP

}

func MPCVerify(mrp *MPCRangeProof, EC CryptoParams) bool {
	m := len(mrp.Comms)
	bitsPerValue := EC.V / m

	//changes:
	// check 1 changes since it includes all commitments
	// check 2 commitment generation is also different

	// verify the challenges
	chal1s256 := sha256.Sum256([]byte(mrp.A.X.String() + mrp.A.Y.String()))
	cy := new(big.Int).SetBytes(chal1s256[:])
	if cy.Cmp(mrp.Cy) != 0 {
		fmt.Println("MPCVerify - Challenge Cy failing!")
		return false
	}
	chal2s256 := sha256.Sum256([]byte(mrp.S.X.String() + mrp.S.Y.String()))
	cz := new(big.Int).SetBytes(chal2s256[:])
	if cz.Cmp(mrp.Cz) != 0 {
		fmt.Println("MPCVerify - Challenge Cz failing!")
		return false
	}
	chal3s256 := sha256.Sum256([]byte(mrp.T1.X.String() + mrp.T1.Y.String() + mrp.T2.X.String() + mrp.T2.Y.String()))
	cx := new(big.Int).SetBytes(chal3s256[:])
	if cx.Cmp(mrp.Cx) != 0 {
		fmt.Println("MPCVerify - Challenge Cx failing!")
		return false
	}

	// given challenges are correct, very range proof
	PowersOfY := PowerVector(EC.V, cy, EC)

	// t_hat * G + tau * H
	lhs := EC.G.Mult(mrp.Th, EC).Add(EC.H.Mult(mrp.Tau, EC), EC)

	// z^2 * \bold{z}^m \bold{V} + delta(y,z) * G + x * T1 + x^2 * T2
	CommPowers := EC.Zero()
	PowersOfZ := PowerVector(m, cz, EC)
	z2 := new(big.Int).Mod(new(big.Int).Mul(cz, cz), EC.N)

	for j := 0; j < m; j++ {
		CommPowers = CommPowers.Add(mrp.Comms[j].Mult(new(big.Int).Mul(z2, PowersOfZ[j]), EC), EC)
	}

	rhs := EC.G.Mult(DeltaMRP(PowersOfY, cz, m, EC), EC).Add(
		mrp.T1.Mult(cx, EC), EC).Add(
		mrp.T2.Mult(new(big.Int).Mul(cx, cx), EC), EC).Add(CommPowers, EC)

	if !lhs.Equal(rhs) {
		fmt.Println("MPCVerify - Uh oh! Check line (63) of verification")
		fmt.Println(rhs)
		fmt.Println(lhs)
		return false
	}

	tmp1 := EC.Zero()
	zneg := new(big.Int).Mod(new(big.Int).Neg(cz), EC.N)
	for i := range EC.BPG {
		tmp1 = tmp1.Add(EC.BPG[i].Mult(zneg, EC), EC)
	}

	PowerOfTwos := PowerVector(bitsPerValue, big.NewInt(2), EC)
	tmp2 := EC.Zero()
	// generate h'
	HPrime := make([]ECPoint, len(EC.BPH))

	for j := 0; j < m; j++ {
		for i := 0; i < bitsPerValue; i++ {
			HPrime[j*bitsPerValue+i] = EC.BPH[j*bitsPerValue+i].Mult(new(big.Int).ModInverse(PowersOfY[j*bitsPerValue+i], EC.N), EC)
		}
	}

	for j := 0; j < m; j++ {
		for i := 0; i < bitsPerValue; i++ {
			val1 := new(big.Int).Mul(cz, PowersOfY[j*bitsPerValue+i])
			zp := new(big.Int).Exp(cz, big.NewInt(2+int64(j)), EC.N)
			val2 := new(big.Int).Mod(new(big.Int).Mul(zp, PowerOfTwos[i]), EC.N)
			tmp2 = tmp2.Add(HPrime[j*bitsPerValue+i].Mult(new(big.Int).Add(val1, val2), EC), EC)
		}
	}

	// without subtracting this value should equal muCH + l[i]G[i] + r[i]H'[i]
	// we want to make sure that the innerproduct checks out, so we subtract it
	P := mrp.A.Add(mrp.S.Mult(cx, EC), EC).Add(tmp1, EC).Add(tmp2, EC).Add(EC.H.Mult(mrp.Mu, EC).Neg(EC), EC)
	//fmt.Println(P)

	if !InnerProductVerifyFast(mrp.Th, P, EC.U, EC.BPG, HPrime, mrp.IPP, EC) {
		fmt.Println("MPCVerify - Uh oh! Check line (65) of verification!")
		return false
	}

	return true
}
