package main

import (
	"fmt"
	"log"
	"math/rand"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	fr_bn254 "github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

const (
	PrivateVecLength = 100
	DummyVecLength   = 60
	PublicThreshold  = 2000
	ClientNum        = 100
)

func PolyEval(vec []fr_bn254.Element, r fr_bn254.Element) fr_bn254.Element {
	prod := vec[0]
	prod.Add(&prod, &r)
	for i := 1; i < len(vec); i++ {
		tmp := vec[i]
		tmp.Add(&tmp, &r)
		prod.Mul(&prod, &tmp)
	}
	return prod
}

func PolyEvalInCircuit(api frontend.API, vec []frontend.Variable, publicR frontend.Variable) frontend.Variable {
	prod := api.Add(vec[0], publicR)
	for i := 1; i < len(vec); i++ {
		prod = api.Mul(prod, api.Add(vec[i], publicR))
	}
	return prod
}

type AddrSumCheckCircuit struct {
	PrivateSrc      []frontend.Variable
	PrivateDst      []frontend.Variable
	PrivateAmount   []frontend.Variable
	PublicThreshold frontend.Variable `gnark:",public"`

	// The following are for the polynomial evaluation
	DummyVec   []frontend.Variable
	PublicR    frontend.Variable `gnark:",public"`
	PublicProd frontend.Variable `gnark:",public"`
}

func (circuit *AddrSumCheckCircuit) Define(api frontend.API) error {
	//assert error if privateVec is empty

	for i := 0; i < PrivateVecLength; i++ {
		current_addr := circuit.PrivateDst[i]
		current_amount := frontend.Variable(0)
		for j := 0; j < PrivateVecLength; j++ {
			diff := api.Sub(current_addr, circuit.PrivateDst[j])
			diff_is_zero := api.IsZero(diff)
			current_amount = api.Add(current_amount, api.Mul(diff_is_zero, circuit.PrivateAmount[j]))
		}
		api.AssertIsLessOrEqual(current_amount, circuit.PublicThreshold)
	}

	// The following is for the polynomial evaluation
	privateProd := PolyEvalInCircuit(api, circuit.PrivateDst, circuit.PublicR)
	privateProd = api.Mul(privateProd, PolyEvalInCircuit(api, circuit.PrivateSrc, circuit.PublicR))
	privateProd = api.Mul(privateProd, PolyEvalInCircuit(api, circuit.PrivateAmount, circuit.PublicR))
	privateProd = api.Mul(privateProd, PolyEvalInCircuit(api, circuit.DummyVec, circuit.PublicR))
	api.AssertIsEqual(privateProd, circuit.PublicProd)

	return nil
}

// generate a random element in fr_bn254
func randomFr() fr_bn254.Element {
	var e fr_bn254.Element
	e.SetRandom()
	return e
}

type Transaction struct {
	src fr_bn254.Element
	dst fr_bn254.Element
	amt fr_bn254.Element
}

type ClientSubmissionToShuffler struct {
	transactions [PrivateVecLength]Transaction
	dummyVec     [DummyVecLength]fr_bn254.Element
}

type ClientSubmissionToServer struct {
	publicWitness *witness.Witness
	publicProd    fr_bn254.Element
	proof         groth16.Proof
}

func asb(asdf uint64, asd uint64) (uint64, uint64) {
	return asdf, asd
}

func RandomTransferWithProof(publicRFr fr_bn254.Element, ccs *frontend.CompiledConstraintSystem, pk *groth16.ProvingKey) (ClientSubmissionToShuffler, ClientSubmissionToServer) {
	// just create a private Vec
	var privateSrcFr [PrivateVecLength]fr_bn254.Element
	var privateSrc [PrivateVecLength]frontend.Variable
	var privateDstFr [PrivateVecLength]fr_bn254.Element
	var privateDstUInt [PrivateVecLength]uint64
	var privateDst [PrivateVecLength]frontend.Variable
	var privateAmountFr [PrivateVecLength]fr_bn254.Element
	var privateAmount [PrivateVecLength]frontend.Variable
	var privateAmountUInt [PrivateVecLength]uint64
	var transactionVec [PrivateVecLength]Transaction

	for i := 0; i < PrivateVecLength; i++ {
		privateSrcFr[i] = randomFr()
		privateSrc[i] = frontend.Variable(privateSrcFr[i])

		privateDstUInt[i] = uint64(rand.Intn(1000))
		privateDstFr[i] = fr_bn254.NewElement(privateDstUInt[i])
		privateDst[i] = frontend.Variable(privateDstFr[i])

		//privateAmountFr[i] = fr_bn254.NewElement(uint64(rand.Intn(300)))
		privateAmountUInt[i] = uint64(200)
		privateAmountFr[i] = fr_bn254.NewElement(privateAmountUInt[i])
		privateAmount[i] = frontend.Variable(privateAmountFr[i])

		transactionVec[i] = Transaction{privateSrcFr[i], privateDstFr[i], privateAmountFr[i]}
	}

	//sort.Slice(privateDstUInt[:], func(i, j int) bool { return privateDstUInt[i] < privateDstUInt[j] })

	//cnt := privateVecFr[0]
	//for i := 1; i < len(privateVecFr); i++ {
	//	cnt.Add(&cnt, &privateVecFr[i])
	//	}
	//fmt.Printf("cnt: %v\n", cnt.Uint64())
	//assert.Equal()
	//fmt.Println("privateDstFr: ", privateDstUInt)
	//fmt.Println("privateAmountFr: ", privateAmountUInt)

	var dummyVecFr [DummyVecLength]fr_bn254.Element
	var dummyVec [DummyVecLength]frontend.Variable
	for i := 0; i < len(dummyVecFr); i++ {
		//dummyVecFr[i].SetUint64(uint64(i * 10))
		dummyVecFr[i] = randomFr()
		//dummyVecFr[i] = fr_bn254.NewElement(uint64(i * 10))
		dummyVec[i] = frontend.Variable(dummyVecFr[i])
	}

	//publicRFr := fr_bn254.NewElement(uint64(1))
	//publicRFr := randomFr()
	publicR := frontend.Variable(publicRFr)
	privateDstProdFr := PolyEval(privateDstFr[:], publicRFr)
	privateSrcProdFr := PolyEval(privateSrcFr[:], publicRFr)
	privateAmountProdFr := PolyEval(privateAmountFr[:], publicRFr)
	dummyProdFr := PolyEval(dummyVecFr[:], publicRFr)
	var publicProdFr fr_bn254.Element
	publicProdFr.Mul(&privateDstProdFr, &dummyProdFr)
	publicProdFr.Mul(&publicProdFr, &privateSrcProdFr)
	publicProdFr.Mul(&publicProdFr, &privateAmountProdFr)
	publicProd := frontend.Variable(publicProdFr)

	// witness definition
	assignment := AddrSumCheckCircuit{
		PrivateSrc:      privateSrc[:],
		PrivateDst:      privateDst[:],
		PrivateAmount:   privateAmount[:],
		PublicThreshold: frontend.Variable(fr_bn254.NewElement(uint64(PublicThreshold))),
		DummyVec:        dummyVec[:],
		PublicR:         publicR,
		PublicProd:      publicProd,
	}

	//fmt.Printf("assignment: %v", assignment)

	witness, witness_err := frontend.NewWitness(&assignment, ecc.BN254)
	if witness_err != nil {
		fmt.Printf("witness_err: %v\n", witness_err)
	}
	///fmt.Println("witness: ", witness)
	//fmt.Printf("assignment: %v", assignment)
	publicWitness, _ := witness.Public()
	//panic("pass")

	// groth16: Prove & Verify
	proof, _ := groth16.Prove(*ccs, *pk, witness)

	submissionToShuffler := ClientSubmissionToShuffler{
		transactions: transactionVec,
		dummyVec:     dummyVecFr,
	}

	submissionToServer := ClientSubmissionToServer{
		publicWitness: publicWitness,
		publicProd:    publicProdFr,
		proof:         proof,
	}

	return submissionToShuffler, submissionToServer
}

func main() {
	/*
		var a, b fr_bn254.Element
		a.SetInt64(1)
		b.SetInt64(1)
		a.Add(&a, &b)
		fmt.Printf("a: %v\n", a)
		c := a.Uint64()
		fmt.Printf("c: %v\n", c)
		return
	*/

	// the server is defining the circuit

	var privateDst [PrivateVecLength]frontend.Variable
	var privateSrc [PrivateVecLength]frontend.Variable
	var privateAmount [PrivateVecLength]frontend.Variable
	var dummyVec [DummyVecLength]frontend.Variable
	for i := 0; i < PrivateVecLength; i++ {
		privateSrc[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
		privateDst[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
		privateAmount[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
	}
	for i := 0; i < len(dummyVec); i++ {
		dummyVec[i] = frontend.Variable(fr_bn254.NewElement(uint64(0)))
	}
	//for i := 0; i < len(array); i++ {
	//	array[i] = frontend.Variable(fr_bn254.NewElement(uint64(i)))
	//	}

	//array := [...]frontend.Variable{1, 2, 3, 4, 5}
	var circuit = AddrSumCheckCircuit{
		PrivateSrc:      privateSrc[:],
		PrivateDst:      privateDst[:],
		PrivateAmount:   privateAmount[:],
		PublicThreshold: 0,
		DummyVec:        dummyVec[:],
		PublicR:         0,
		PublicProd:      0,
	}
	//ccs, _ := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	start := time.Now()
	ccs, _ := frontend.Compile(ecc.BN254, r1cs.NewBuilder, &circuit)

	// groth16 zkSNARK: Setup
	pk, vk, _ := groth16.Setup(ccs)
	setup_time := time.Since(start)

	start = time.Now()
	publicRFr := randomFr()
	//publicRFr := fr_bn254.NewElement(uint64(1))

	// for clients, each client has a private value
	var allSecretVal []fr_bn254.Element
	var allDummyVal []fr_bn254.Element
	var allProof []ClientSubmissionToServer

	// this counted as proving time
	for i := 0; i < ClientNum; i++ {
		//var secretVal uint64
		toShuffler, toServer := RandomTransferWithProof(publicRFr, &ccs, &pk)
		for j := 0; j < PrivateVecLength; j++ {
			allSecretVal = append(allSecretVal, toShuffler.transactions[j].src, toShuffler.transactions[j].dst, toShuffler.transactions[j].amt)
		}
		//allSecretVal = append(allSecretVal, toShuffler.privateVec[:]...)
		allDummyVal = append(allDummyVal, toShuffler.dummyVec[:]...)
		allProof = append(allProof, toServer)
	}

	proving_time := time.Since(start)
	start = time.Now()

	//the server now sees all the secret values and dummy values
	// it first verifies all the proof
	// it also computes the product of all the publicProd
	prodFromClients := fr_bn254.NewElement(uint64(1))
	for i := 0; i < ClientNum; i++ {
		//verify proof
		//fmt.Printf("proof: %v
		verification_err := groth16.Verify(allProof[i].proof, vk, allProof[i].publicWitness)
		if verification_err != nil {
			fmt.Printf("verification error in client %v", i)
		}
		prodFromClients.Mul(&prodFromClients, &allProof[i].publicProd)
	}

	// it then computes the product from shufflers
	prodFromShuffler := PolyEval(allSecretVal, publicRFr)
	dummyProdFromShuffler := PolyEval(allDummyVal, publicRFr)
	prodFromShuffler.Mul(&prodFromShuffler, &dummyProdFromShuffler)
	if prodFromShuffler.Equal(&prodFromClients) {
		fmt.Printf("server: the set from clients is the same as the set from shuffler\n")
	} else {
		fmt.Printf("server: the set from clients is NOT the same as the set from shuffler\n")
	}

	verifying_time := time.Since(start)

	// the server then computes the sum of all the secret values
	/*
		sum := fr_bn254.NewElement(uint64(0))
		for i := 0; i < len(allSecretVal); i++ {
			sum.Add(&sum, &allSecretVal[i])
		}
		fmt.Printf("The computed sum is %v\n", sum.Uint64())
	*/

	log.Printf("setup time: %v\n", setup_time)
	log.Printf("proving time: %v\n", proving_time)
	log.Printf("Per client proving time: %v\n", proving_time/ClientNum)
	log.Printf("verifying time: %v\n", verifying_time)

	/*
		// just create a private Vec

		var privateValFr = fr_bn254.NewElement(uint64(14))
		var privateVecFr [5]fr_bn254.Element
		var privateVec [5]frontend.Variable
		privateVecFr[0] = privateValFr
		for i := 1; i < len(privateVecFr); i++ {
			privateVecFr[i] = randomFr()
			privateVec[i] = frontend.Variable(privateVecFr[i])
			privateVecFr[0].Sub(&privateVecFr[0], &privateVecFr[i])
		}
		privateVec[0] = frontend.Variable(privateVecFr[0])

		cnt := privateVecFr[0]
		for i := 1; i < len(privateVecFr); i++ {
			cnt.Add(&cnt, &privateVecFr[i])
		}
		fmt.Printf("cnt: %v\n", cnt.Uint64())

		var dummyVecFr [2]fr_bn254.Element
		var dummyVec [2]frontend.Variable
		for i := 0; i < len(dummyVecFr); i++ {
			dummyVecFr[i].SetUint64(uint64(i * 10))
			dummyVec[i] = frontend.Variable(dummyVecFr[i])
		}

		//publicRFr := fr_bn254.NewElement(uint64(1))
		publicRFr := randomFr()
		publicR := frontend.Variable(publicRFr)
		privateProdFr := PolyEval(privateVecFr[:], publicRFr)
		dummyProdFr := PolyEval(dummyVecFr[:], publicRFr)
		var publicProdFr fr_bn254.Element
		publicProdFr.Mul(&privateProdFr, &dummyProdFr)
		publicProd := frontend.Variable(publicProdFr)

		//convert dummyVecFr to Variable
		var dummyVecVar [len(dummyVecFr)]frontend.Variable
		for i := 0; i < len(dummyVecFr); i++ {
			dummyVecVar[i] = frontend.Variable(dummyVecFr[i])
		}

		//convert privateVecFr to Variable
		var privateVecVar [5]frontend.Variable
		for i := 0; i < len(privateVecFr); i++ {
			privateVecVar[i] = frontend.Variable(privateVecFr[i])
		}

		//TODO: add a random sample in Fr
		//TODO: convert to Variable

		// witness definition
		assignment := sumAndCmpCircuit{
			PrivateVec:      privateVecVar[:],
			PublicThreshold: frontend.Variable(fr_bn254.NewElement(uint64(15))),
			DummyVec:        dummyVecVar[:],
			PublicR:         publicR,
			PublicProd:      publicProd,
		}
		witness, _ := frontend.NewWitness(&assignment, ecc.BN254)
		fmt.Println(witness)
		publicWitness, _ := witness.Public()

		// groth16: Prove & Verify
		proof, proof_err := groth16.Prove(ccs, pk, witness)
		fmt.Printf("proof error: %v\n", proof_err)

		verification_err := groth16.Verify(proof, vk, publicWitness)

		fmt.Printf("verification error: %v\n", verification_err)
	*/
}
