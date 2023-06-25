package main

import (
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	fr_bn254 "github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// Circuit defines a pre-image knowledge proof
// mimc(secret preImage) = public hash
type dummy struct {
	X frontend.Variable
}

// Circuit defines a simple circuit
type Circuit struct {
	D dummy
	//X frontend.Variable
	Y frontend.Variable `gnark:",public"`
}

// Define declares the circuit constraints
// x**3 + x + 5 == y
func (circuit *Circuit) Define(api frontend.API) error {
	x3 := api.Mul(circuit.D.X, circuit.D.X, circuit.D.X)
	api.AssertIsEqual(circuit.Y, api.Add(x3, circuit.D.X, 5))
	//api.AssertIsEqual(circuit.D.X, circuit.Y)
	return nil
}

// x == y

func TestIDK(t *testing.T) {
	assert := test.NewAssert(t)

	var cubicCircuit Circuit

	assert.ProverFailed(&cubicCircuit, &Circuit{
		D: dummy{
			X: 42,
		},
		Y: 43,
	}, test.WithCurves(ecc.BN254))

	assert.ProverSucceeded(&cubicCircuit, &Circuit{
		D: dummy{
			X: frontend.Variable(fr_bn254.NewElement(3)),
		},
		Y: frontend.Variable(fr_bn254.NewElement(35)),
	}, test.WithCurves(ecc.BN254))
}
