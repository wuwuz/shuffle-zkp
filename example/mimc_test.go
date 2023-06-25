package main

import (
	"fmt"
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	fr_bn254 "github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/hash"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/hash/mimc"
	"github.com/consensys/gnark/test"
)

// Circuit defines a pre-image knowledge proof
// mimc(secret preImage) = public hash
type Circuit struct {
	// struct tag on a variable is optional
	// default uses variable name and secret visibility.
	PreImage frontend.Variable
	Hash     frontend.Variable `gnark:",public"`
}

// Define declares the circuit's constraints
// Hash = mimc(PreImage)
func (circuit *Circuit) Define(api frontend.API) error {
	// hash function
	mimc, _ := mimc.NewMiMC(api)

	// specify constraints
	// mimc(preImage) == hash
	mimc.Write(circuit.PreImage)
	api.AssertIsEqual(circuit.Hash, mimc.Sum())

	return nil
}

func TestPreimage(t *testing.T) {
	assert := test.NewAssert(t)

	var mimcCircuit Circuit

	assert.ProverFailed(&mimcCircuit, &Circuit{
		Hash:     42,
		PreImage: 42,
	})

	a := big.NewInt(123456)
	fmt.Printf("a: %v\n", a.Bytes())
	a_bytes := make([]byte, 32)
	// set a_bytes to a with big endian convention
	copy(a_bytes[32-len(a.Bytes()):], a.Bytes()) // big endian
	//copy(a_bytes[:], a.Bytes()) // big endian

	goMimc := hash.MIMC_BN254.New()
	goMimc.Write(a_bytes)
	a_hash := goMimc.Sum(nil)
	fmt.Printf("a_hash: %v\n", a_hash)
	a_hash_fr := fr_bn254.NewElement(1)
	a_hash_fr.SetBytes(a_hash)
	a_hash_var := frontend.Variable(a_hash_fr)

	fmt.Printf("a_hash_var: %v\n", a_hash_var)

	assert.ProverSucceeded(&mimcCircuit, &Circuit{
		Hash:     a_hash_var,
		PreImage: frontend.Variable(123456),
	}, test.WithCurves(ecc.BN254))

	assert.ProverSucceeded(&mimcCircuit, &Circuit{
		PreImage: "16130099170765464552823636852555369511329944820189892919423002775646948828469",
		Hash:     "12886436712380113721405259596386800092738845035233065858332878701083870690753",
	}, test.WithCurves(ecc.BN254))

}
