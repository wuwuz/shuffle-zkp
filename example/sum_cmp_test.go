package main

import (
	"testing"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

func TestSumAndCmpCircuit(t *testing.T) {
	assert := test.NewAssert(t)

	var definingCircuit = sumAndCmpCircuit{
		PrivateVec:      []frontend.Variable{0, 0, 0, 0, 0},
		PublicThreshold: frontend.Variable(0),
	}

	assert.ProverFailed(&definingCircuit, &sumAndCmpCircuit{
		PrivateVec:      []frontend.Variable{1, 2, 3, 4, 5},
		PublicThreshold: frontend.Variable(10),
	})

	assert.ProverSucceeded(&definingCircuit, &sumAndCmpCircuit{
		PrivateVec:      []frontend.Variable{1, 2, 3, 4, 5},
		PublicThreshold: frontend.Variable(15),
	})
}
