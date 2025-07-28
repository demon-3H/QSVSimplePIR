package pir
import (
	"os"
	"testing"
)

const LOGQ = uint64(32)
const SEC_PARAM = uint64(1 << 10)

// Test SimplePIR
func TestSimplePir(t *testing.T) {
	file, err := os.Create("output.txt")
	if err != nil {
		panic(err)
	}
	defer file.Close()
	os.Stdout = file
	N := uint64(1 << 24)
	d := uint64(64)
	pir := SimplePIR{}
	p := pir.PickParams(N, d, SEC_PARAM, LOGQ)
	DB := MakeRandomDB(N, d, &p)
	RunPIR(&pir, DB, p, []uint64{262144})
}
// Test QSVSimplePIR 
func TestQSVSimplePIR (t *testing.T) {
	// file, err := os.Create("outputm.txt")
	// if err != nil {
	// 	panic(err)
	// }
	// defer file.Close()
	// os.Stdout = file
	N := uint64(1 << 24)
	d := uint64(64)
	pir := SimplePIR{}
	p := pir.PickParams(N, d, SEC_PARAM, LOGQ)
	DB := MakeRandomDB(N, d, &p)
	// QSV(p)
	RunPIR(&pir, DB, p, []uint64{7})
}

// Using error vectors to validate QSV.
func TestQSV(t *testing.T) {
	// file, err := os.Create("outputm.txt")
	// if err != nil {
	// 	panic(err)
	// }
	// defer file.Close()
	// os.Stdout = file
	N := uint64(1 << 24)
	d := uint64(64)
	pir := SimplePIR{}
	p := pir.PickParams(N, d, SEC_PARAM, LOGQ)
	QSV2(p)
}
