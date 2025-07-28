package pir

// #cgo CFLAGS: -O3 -march=native
// #include "pir.h"
import 	"C"
import (
	"fmt"
	"math"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"log"

    "time"
	"unsafe"
)
func QSV(p Params,A *Matrix,secret *Matrix,err *Matrix,qindex int) uint64{
	// 生成公钥、私钥、噪声
	// A := MatrixRand(p.M, p.N, p.Logq, 0)

	// fmt.Printf("生成公钥A\n")
	// secret := MatrixRand(p.N, 1, p.Logq, 0)
	// fmt.Printf("生成私钥s\n")
	secret_bak := convertToIntSlice(secret.Data )
	start := time.Now()
	// err := MatrixGaussian(p.M, 1)
	err_tmp := convertToIntSlice(err.Data )
	fmt.Printf("生成噪声e\n")

	//查询明文向量 
	// qindex:=11
	plaint := oneHot(int(p.M),qindex)

	//查询密文向量
	query := MatrixMul(A, secret)
	query.MatrixAdd(err)
	query.Data[qindex%int(p.M)] += C.Elem(p.Delta())
	fmt.Printf("查询向量m\n")
	fmt.Printf("密文查询向量u\n")
		
	maxLen := max(len(plaint), len(secret_bak))
	secret_tmp := padWithZeros(secret_bak, maxLen)
	

	// 承若t1、t2、t3、v1
	fmt.Printf("\n\033[32m--------------证明者执行证明程序--------------\033[0m\n")
	t1_tmp :=  MatrixRand(p.M, 1, p.Logq, 0)
	t1 := convertToIntSlice(t1_tmp.Data )
	fmt.Printf("生成随机t1\n")
	t2_tmp :=  MatrixRand(p.N, 1, p.Logq, 0)
	t2_bak := convertToIntSlice(t2_tmp.Data )
	fmt.Printf("生成随机t2\n")
	t3_tmp :=  MatrixRand(p.M, 1, p.Logq, 0)
	t3 := convertToIntSlice(t3_tmp.Data )
	fmt.Printf("生成随机t3\n")
	v1 :=vecmul(t1,t1)
	fmt.Printf("计算v1\n")
	w1_tmp:= MatrixMul(A, t2_tmp)
	w1_tmp1:= convertToIntSlice(w1_tmp.Data )
	w1_tmp2:= vecadd(w1_tmp1,t1)
	w1_tmp3:= vecadd(w1_tmp2,t3)
	w1:= vecmul(w1_tmp3,w1_tmp3)
	
	fmt.Printf("计算w1\n")
	r1_tmp :=  MatrixRand(p.M, 1, p.Logq, 0)
	r1 := convertToIntSlice(r1_tmp.Data )
	fmt.Printf("生成随机r1\n")

	t2 := padWithZeros(t2_bak, maxLen)
	fmt.Printf("对t1,t2,t3,v1,w1,r1进行rs运算，获得h1\n")
	h1:=vrs(0,t1 ,t2 ,t3 ,v1,w1,r1 )
	// for i,tmp_a:=  range h1 {
	// 	fmt.Printf("h1的第%d行: %v\n",i,  tmp_a)
	// }



	// 承若m、s、e、v0、w0
	Delta_m:=mulScalar(plaint,p.Delta())
	fmt.Printf("计算Delta_m\n")
	plaint_tmp:=mulScalar(plaint,2)
	plaint_tmp1 :=subScalar(plaint_tmp,1)
	Delta_m_tmp2 :=mulScalar(plaint_tmp1,p.Delta())
	v0:=vecmul(t1,Delta_m_tmp2)
	fmt.Printf("计算v0\n")
	w0 :=make([]uint64, p.M)
	fmt.Printf("计算w0\n")
	r0_tmp :=  MatrixRand(p.M, 1, p.Logq, 0)
	r0 := convertToIntSlice(r0_tmp.Data )
	fmt.Printf("生成随机r0\n")
	fmt.Printf("对m,s,e,v0,w0,r0进行rs运算，获得h0\n")
	h0:=vrs(0,Delta_m ,secret_tmp,err_tmp,v0 ,w0,r0)
	// for i,tmp_a:=  range h0 {
	// 	fmt.Printf("h0的第%d行: %v\n",i,  tmp_a)
	// }
	
	fmt.Printf("生成承若M\n")
	merged := mergeMatrices(h1, h0)
	var roots [][]byte
	var vleaves [][][]byte
	for _,v1:= range merged{
		// fmt.Printf("h0的 %v\n", v1)
		var leaves [][]byte
		for _, v2 := range v1 {
			h := hashVector(v2)
			leaves = append(leaves, h)
		}
		vleaves = append(vleaves, leaves)
		root := buildMerkleTree(leaves)
		roots = append(roots, root)
	}
	M:= buildMerkleTree(roots)
	fmt.Printf("Merkle Root: %s\n", hex.EncodeToString(M))
	// for i, r := range roots {
	// 	fmt.Printf("承若M的第%d行 root: %v\n", i, r)
	// }
	fmt.Printf("\033[34mP----------->V\033[0m:发送承若M,发送查询向量\n")
	// traffic_en := 8 * float64(len(roots[0])*len(roots))/float64(8*1024)
	traffic := float64(len(M))/float64(1024)
	fmt.Printf("%d",len(roots))
	//响应挑战值
	fmt.Printf("\n\033[32m--------------验证开始--------------\033[0m\n")
	change:=uint64(5)
	traffic1 := 8 * float64(maxLen)/float64(1024)
	fmt.Printf("验证者生成挑战值%d\n",change)
	fmt.Printf("\033[34mV----------->P\033[0m:发送挑战值x\n")

	fmt.Printf("\n\033[32m--------------证明者响应挑战--------------\033[0m\n")
	f1_tmp:=vrs(change,Delta_m,t1 )	
	f1:=extractColumn(f1_tmp,0)
	fmt.Printf("证明者计算f1\n")
	f2_tmp:=vrs(change,secret_tmp,t2 )
	f2_bak:=vrs(change,secret_bak,t2_bak )
	f2:=extractColumn(f2_tmp,0)
	f2_bak1:=extractColumn(f2_bak,0)
	fmt.Printf("证明者计算f2\n")
	f3_tmp:=vrs(change,err_tmp,t3 )
	f3:=extractColumn(f3_tmp,0)
	fmt.Printf("证明者计算f3\n")
	tmp:=subScalar(f1,p.Delta())
	tmp1:=vecmul(f1,tmp)
	tmp2:=divScalar(tmp1,5)
	fmt.Printf("证明者计算布尔约束值t\n")
	out := MatrixNew(p.N, 1)
	
	for i := 0; i < len(f2_bak1); i++ {
		out.Data[i] = C.Elem(f2[i])
	}
	d2_tmp:=MatrixMul(A,out )
	d2:= convertToIntSlice(d2_tmp.Data )
	d2 = padWithZeros(d2, maxLen)
	u:=convertToIntSlice(query.Data )
	d_tmp:=vecsub(u,d2)
	d_tmp1:=vecsub(d_tmp,f1)
	d_tmp2:=vecsub(d_tmp1,f3)
	d_tmp3:=vecmul(d_tmp2,d_tmp2)
	d:=divScalar(d_tmp3,change)
	fmt.Printf("证明者计算一致性约束值d\n")
	r_tmp:=vrs(change,r0,r1 )
	r:=extractColumn(r_tmp,0)
	fmt.Printf("证明者计算随机值r\n")

	//响应路径
	h11:=extractColumn(h1,1)
	h21:=extractColumn(h0,1)
	fmt.Printf("证明者提取h1的路径值\n")
	fmt.Printf("证明者提取h0的路径值\n")
	fmt.Printf("\033[34mP----------->V\033[0m:f1,f2,f3,t,d,r以及h1,h0对应路径值\n")
	traffic2 := float64(len(f1)+len(f2)+len(f3)+len(r)+len(h11)+len(h21))/float64(1024)
	
	fmt.Printf("\n\033[32m--------------验证者验证h1,h0对应路径值是否正确--------------\033[0m\n")

	var roots_tmp [][]byte
	proof_size:=float64(0)
	for _, leaves := range vleaves {
		indexToProve := 1
		proof := generateMerkleProof(indexToProve, leaves)
		proof_size=float64(unsafe.Sizeof(proof))
		// fmt.Printf(" %d Size of x: %d bytes\n",i, unsafe.Sizeof(proof))
		roots_tmp1 := verifyMerkleProof(leaves[indexToProve], proof)
		roots_tmp=append(roots_tmp,roots_tmp1)
	}
	traffic3 := proof_size*float64(len(vleaves))/float64(1024)
	M1:= buildMerkleTree(roots_tmp)
	
	fmt.Printf("Merkle Root: %s\n", hex.EncodeToString(M1))
	fmt.Printf("\n\033[32m--------------验证者计算等式两边结果--------------\033[0m\n")
	if EqualBytes(M,M1){
		fmt.Printf("承若验证通过")
	} else{
		return 1
	}
	//计算等式右边
	right :=vrs(change,h21, h11 )
	right1:=extractColumn(right,0)

	//计算等式左边
	left :=vrs(0,f1 ,f2 ,f3 ,tmp2 ,d,r)
	left1:=extractColumn(left,1)
	
	fmt.Printf("总通信量为%2fKB\n",traffic+traffic1+traffic2+traffic3)
	elapsed := time.Since(start)
    fmt.Println("运行时间:", elapsed)
	if allEqual(right1,left1){
		fmt.Printf("验证通过\n")
		return 0
	}else{
		fmt.Printf("验证失败\n")
		return 1
	}
}
func QSV2(p Params){
	// 生成公钥、私钥、噪声
	A := MatrixRand(p.M, p.N, p.Logq, 0)

	fmt.Printf("生成公钥A\n")
	secret := MatrixRand(p.N, 1, p.Logq, 0)
	fmt.Printf("生成私钥s\n")
	secret_bak := convertToIntSlice(secret.Data )
	start := time.Now()
	err := MatrixGaussian(p.M, 1)
	err_tmp := convertToIntSlice(err.Data )
	fmt.Printf("生成噪声e\n")

	//查询明文向量 
	qindex:=11
	plaint := oneHot(int(p.M),qindex)

	//查询密文向量
	query := MatrixMul(A, secret)
	query.MatrixAdd(err)
	query.Data[qindex%int(p.M)] += C.Elem(p.Delta())
	fmt.Printf("查询向量m\n")
	fmt.Printf("密文查询向量u\n")
		
	maxLen := max(len(plaint), len(secret_bak))
	secret_tmp := padWithZeros(secret_bak, maxLen)
	

	// 承若t1、t2、t3、v1
	fmt.Printf("\n\033[32m--------------证明者执行证明程序--------------\033[0m\n")
	t1_tmp :=  MatrixRand(p.M, 1, p.Logq, 0)
	t1 := convertToIntSlice(t1_tmp.Data )
	fmt.Printf("生成随机t1\n")
	t2_tmp :=  MatrixRand(p.N, 1, p.Logq, 0)
	t2_bak := convertToIntSlice(t2_tmp.Data )
	fmt.Printf("生成随机t2\n")
	t3_tmp :=  MatrixRand(p.M, 1, p.Logq, 0)
	t3 := convertToIntSlice(t3_tmp.Data )
	fmt.Printf("生成随机t3\n")
	v1 :=vecmul(t1,t1)
	fmt.Printf("计算v1\n")
	w1_tmp:= MatrixMul(A, t2_tmp)
	w1_tmp1:= convertToIntSlice(w1_tmp.Data )
	w1_tmp2:= vecadd(w1_tmp1,t1)
	w1_tmp3:= vecadd(w1_tmp2,t3)
	w1:= vecmul(w1_tmp3,w1_tmp3)
	
	fmt.Printf("计算w1\n")
	r1_tmp :=  MatrixRand(p.M, 1, p.Logq, 0)
	r1 := convertToIntSlice(r1_tmp.Data )
	fmt.Printf("生成随机r1\n")

	t2 := padWithZeros(t2_bak, maxLen)
	fmt.Printf("对t1,t2,t3,v1,w1,r1进行rs运算，获得h1\n")
	h1:=vrs(0,t1 ,t2 ,t3 ,v1,w1,r1 )
	// for i,tmp_a:=  range h1 {
	// 	fmt.Printf("h1的第%d行: %v\n",i,  tmp_a)
	// }



	// 承若m、s、e、v0、w0
	Delta_m:=mulScalar(plaint,p.Delta())
	fmt.Printf("计算Delta_m\n")
	plaint_tmp:=mulScalar(plaint,2)
	plaint_tmp1 :=subScalar(plaint_tmp,1)
	Delta_m_tmp2 :=mulScalar(plaint_tmp1,p.Delta())
	v0:=vecmul(t1,Delta_m_tmp2)
	fmt.Printf("计算v0\n")
	w0 :=make([]uint64, p.M)
	fmt.Printf("计算w0\n")
	r0_tmp :=  MatrixRand(p.M, 1, p.Logq, 0)
	r0 := convertToIntSlice(r0_tmp.Data )
	fmt.Printf("生成随机r0\n")
	fmt.Printf("对m,s,e,v0,w0,r0进行rs运算，获得h0\n")
	h0:=vrs(0,Delta_m ,secret_tmp,err_tmp,v0 ,w0,r0)
	// for i,tmp_a:=  range h0 {
	// 	fmt.Printf("h0的第%d行: %v\n",i,  tmp_a)
	// }
	
	fmt.Printf("生成承若M\n")
	merged := mergeMatrices(h1, h0)
	var roots [][]byte
	var vleaves [][][]byte
	for _,v1:= range merged{
		// fmt.Printf("h0的 %v\n", v1)
		var leaves [][]byte
		for _, v2 := range v1 {
			h := hashVector(v2)
			leaves = append(leaves, h)
		}
		vleaves = append(vleaves, leaves)
		root := buildMerkleTree(leaves)
		roots = append(roots, root)
	}
	M:= buildMerkleTree(roots)
	fmt.Printf("Merkle Root: %s\n", hex.EncodeToString(M))
	// for i, r := range roots {
	// 	fmt.Printf("承若M的第%d行 root: %v\n", i, r)
	// }
	fmt.Printf("\033[34mP----------->V\033[0m:发送承若M,发送查询向量\n")
	// traffic_en := 8 * float64(len(roots[0])*len(roots))/float64(8*1024)
	traffic := float64(len(M))/float64(1024)
	fmt.Printf("%d",len(roots))
	//响应挑战值
	fmt.Printf("\n\033[32m--------------验证开始--------------\033[0m\n")
	change:=uint64(5)
	traffic1 := 8 * float64(maxLen)/float64(1024)
	fmt.Printf("验证者生成挑战值%d\n",change)
	fmt.Printf("\033[34mV----------->P\033[0m:发送挑战值x\n")

	fmt.Printf("\n\033[32m--------------证明者响应挑战--------------\033[0m\n")
	f1_tmp:=vrs(change,Delta_m,t1 )	
	f1:=extractColumn(f1_tmp,0)
	fmt.Printf("证明者计算f1\n")
	f2_tmp:=vrs(change,secret_tmp,t2 )
	f2_bak:=vrs(change,secret_bak,t2_bak )
	f2:=extractColumn(f2_tmp,0)
	f2_bak1:=extractColumn(f2_bak,0)
	fmt.Printf("证明者计算f2\n")
	f3_tmp:=vrs(change,err_tmp,t3 )
	f3:=extractColumn(f3_tmp,0)
	fmt.Printf("证明者计算f3\n")
	tmp:=subScalar(f1,p.Delta())
	tmp1:=vecmul(f1,tmp)
	tmp2:=divScalar(tmp1,5)
	fmt.Printf("证明者计算布尔约束值t\n")
	out := MatrixNew(p.N, 1)
	
	for i := 0; i < len(f2_bak1); i++ {
		out.Data[i] = C.Elem(f2[i])
	}
	d2_tmp:=MatrixMul(A,out )
	d2:= convertToIntSlice(d2_tmp.Data )
	d2 = padWithZeros(d2, maxLen)
	u:=convertToIntSlice(query.Data )
	d_tmp:=vecsub(u,d2)
	d_tmp1:=vecsub(d_tmp,f1)
	d_tmp2:=vecsub(d_tmp1,f3)
	d_tmp3:=vecmul(d_tmp2,d_tmp2)
	d:=divScalar(d_tmp3,change)
	fmt.Printf("证明者计算一致性约束值d\n")
	r_tmp:=vrs(change,r0,r1 )
	r:=extractColumn(r_tmp,0)
	fmt.Printf("证明者计算随机值r\n")

	//响应路径
	h11:=extractColumn(h1,1)
	h21:=extractColumn(h0,1)
	fmt.Printf("证明者提取h1的路径值\n")
	fmt.Printf("证明者提取h0的路径值\n")
	fmt.Printf("\033[34mP----------->V\033[0m:f1,f2,f3,t,d,r以及h1,h0对应路径值\n")
	traffic2 := float64(len(f1)+len(f2)+len(f3)+len(r)+len(h11)+len(h21))/float64(1024)
	
	fmt.Printf("\n\033[32m--------------验证者验证h1,h0对应路径值是否正确--------------\033[0m\n")

	var roots_tmp [][]byte
	proof_size:=float64(0)
	for _, leaves := range vleaves {
		indexToProve := 1
		proof := generateMerkleProof(indexToProve, leaves)
		proof_size=float64(unsafe.Sizeof(proof))
		// fmt.Printf(" %d Size of x: %d bytes\n",i, unsafe.Sizeof(proof))
		roots_tmp1 := verifyMerkleProof(leaves[indexToProve], proof)
		roots_tmp=append(roots_tmp,roots_tmp1)
	}
	traffic3 := proof_size*float64(len(vleaves))/float64(1024)
	M1:= buildMerkleTree(roots_tmp)
	
	fmt.Printf("Merkle Root: %s\n", hex.EncodeToString(M1))
	fmt.Printf("\n\033[32m--------------验证者计算等式两边结果--------------\033[0m\n")
	if EqualBytes(M,M1){
		fmt.Printf("承若验证通过\n")
	} else{
		fmt.Printf("承若验证不通过\n")
	}
	//计算等式右边
	right :=vrs(change,h21, h11 )
	right1:=extractColumn(right,0)

	//计算等式左边
	left :=vrs(0,f1 ,f2 ,f3 ,tmp2 ,d,r)
	left1:=extractColumn(left,1)
	
	fmt.Printf("总通信量为%2fKB\n",traffic+traffic1+traffic2+traffic3)
	elapsed := time.Since(start)
    fmt.Println("运行时间:", elapsed)
	if allEqual(right1,left1){
		fmt.Printf("验证通过\n")
	}else{
		fmt.Printf("验证失败\n")
	}
}
func EqualBytes(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}
func allEqual(a, b []uint64) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}
func GenerateArray(n uint64) []uint64 {
	if n == 0 {
		return []uint64{}
	}
	arr := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		arr[i] = i + 1
	}
	return arr
}
func mergeMatrices(a, b [][]uint64) [][][]uint64 {
	rows := len(a)
	if rows == 0 || rows != len(b) {
		panic("行数不匹配或为空")
	}
	cols := len(a[0])
	for i := range b {
		if len(b[i]) != cols || len(a[i]) != cols {
			panic("列数不匹配")
		}
	}

	// 初始化三维切片: [rows][cols][2]
	result := make([][][]uint64, rows)
	for i := range result {
		result[i] = make([][]uint64, cols)
		for j := range result[i] {
			result[i][j] = make([]uint64, 2)
		}
	}

	// 填充三维矩阵
	for i := 0; i < rows; i++ {
		for j := 0; j < cols; j++ {
			result[i][j][0] = a[i][j]
			result[i][j][1] = b[i][j]
		}
	}
	return result
}
//路径提取
func extractColumn(matrix [][]uint64, index int) []uint64 {
	column := []uint64{}
	for _, row := range matrix {
		// 简单校验，防止越界
		if index < len(row) {
			column = append(column, row[index])
		}
	}
	return column
}

//明文查询向量生成
func oneHot(x int, y int) []uint64 {
	if y < 0 || y >= x {
		panic("y 超出范围")
	}
	arr := make([]uint64, x)
	fmt.Printf("设置向量其中一个元素为2")
	arr[y] = 2
	return arr
}

func convertToIntSlice(cArr []C.Elem) []uint64 {
	result := make([]uint64, len(cArr))
	for i, v := range cArr {
		result[i] = uint64(v)
	}
	return result
}
// 有限域模数（必须是素数）
const p uint64 =512

// 加法: (a + b) mod p
func add(a, b uint64) uint64 {
	return (a + b) % p
}

// 减法: (a - b + p) mod p
func sub(a, b uint64) uint64 {
	if a >= b {
		return (a - b) % p
	}
	return (a + p - b) % p
}

// 乘法: (a * b) mod p
func mul(a, b uint64) uint64 {
	return (a * b) % p
}

// 求逆元: b^(-1) mod p
func inverse(b uint64) uint64 {
	if b == 0 {
		log.Fatal("除数不能为 0，无法求逆元")
	}
	gcd, x, _ := extendedGCD(uint64(b), uint64(p))
	if gcd != 1 {
		log.Fatalf("Error: %d 在模 %d 下没有逆元", b, p)
	}
	return uint64((x%uint64(p) + uint64(p)) % uint64(p))
}

// 除法: (a / b) mod p
func div(a, b uint64) uint64 {
	return mul(a, inverse(b))
}

// 扩展欧几里得算法
func extendedGCD(a, b uint64) (gcd, x, y uint64) {
	if b == 0 {
		return a, 1, 0
	}
	gcd, x1, y1 := extendedGCD(b, a%b)
	x = y1
	y = x1 - (a/b)*y1
	return
}
func max(x, y int) int {
	if x > y {
			return x
	} else {
			return y
	}
}
func padWithZeros(vec []uint64, targetLen int) []uint64 {
	padLen := targetLen - len(vec)
	if padLen > 0 {
		padding := make([]uint64, padLen)
		vec = append(vec, padding...)
	}
	return vec
}
//向量rs算法
func vrs(change uint64, coeffVectors ...[]uint64) [][]uint64{

	length := len(coeffVectors[0])
	

	result := [][]uint64{}
	for i := 0; i < length; i++ {
		var elementsAtI []uint64
		for _, vec := range coeffVectors {
			elementsAtI = append(elementsAtI, vec[i])	
		}
		
		result=append(result,rs(change,elementsAtI))
	}
	return result
}

//rs算法
func rs(change uint64,coeffs []uint64) []uint64 {

	result := []uint64{}

	// 要计算的输入
	inputs := GenerateArray(uint64(20))
	if change!=0{
        inputs = []uint64{change}
    } 

	// 计算并打印结果
	for _, x := range inputs {
		r := Polynomial(coeffs, x)
		result=append(result,r)
	}
	return result
}

//多项式计算
func Polynomial(coeffs []uint64, x uint64) uint64 {
	result := uint64(0)
	for i, coeff := range coeffs {
		result =add(result, mul(coeff ,uint64(math.Pow(float64(x), float64(i)))))
	}
	return result
}
//向量标量减法
func subScalar(vec []uint64, scalar uint64) []uint64 {
	result := make([]uint64, len(vec))
	for i, v := range vec {
		result[i] = sub(v , scalar)
	}
	return result
}
//向量标量乘法
func mulScalar(vec []uint64, scalar uint64) []uint64 {
	result := make([]uint64, len(vec))
	for i, v := range vec {
		result[i] = mul(v , scalar)
	}
	return result
}
//向量标量除法
func divScalar(vec []uint64, scalar uint64) []uint64 {
	result := make([]uint64, len(vec))
	for i, v := range vec {
		result[i] = div(v , scalar)
	}
	return result
}


//对位乘法法
func vecmul(t1, t2 []uint64) []uint64 {
	
	if len(t1) != len(t2) {
		log.Fatal("两个向量长度不一致")
	}
	result := make([]uint64, len(t1))
	for i := range t1 {
		result[i] = mul(t1[i] , t2[i])
	}
	return result
}
//对位向量减法
func vecsub(t1, t2 []uint64) []uint64 {
	if len(t1) != len(t2) {
		log.Fatal("两个向量长度不一致")
	}
	result := make([]uint64, len(t1))
	for i := range t1 {
		result[i] = sub(t1[i] , t2[i])
	}
	return result
}
//对位向量减法
func vecadd(t1, t2 []uint64) []uint64 {
	if len(t1) != len(t2) {
		log.Fatal("两个向量长度不一致")
	}
	result := make([]uint64, len(t1))
	for i := range t1 {
		result[i] = add(t1[i] , t2[i])
	}
	return result
}



// 将向量编码为字节并哈希
func hashVector(v []uint64) []byte {
	length :=len(v)
	buf := make([]byte, 8*length) // 3 个 uint64，每个 8 字节
	for i := 0; i < length; i++ {
		binary.LittleEndian.PutUint64(buf[i*8:(i+1)*8], v[i])
	}
	hash := sha256.Sum256(buf)
	return hash[:]
}

// 合并两个哈希并再哈希
func hashPair(left, right []byte) []byte {
	data := append(left, right...)
	sum := sha256.Sum256(data)
	return sum[:]
}

// 构建 Merkle 树，返回根哈希
func buildMerkleTree(hashes [][]byte) []byte {
	if len(hashes) == 0 {
		return nil
	}
	for len(hashes) > 1 {
		var nextLevel [][]byte
		for i := 0; i < len(hashes); i += 2 {
			left := hashes[i]
			var right []byte
			if i+1 < len(hashes) {
				right = hashes[i+1]
			} else {
				right = left // 奇数节点复制自身
			}
			combined := hashPair(left, right)
			nextLevel = append(nextLevel, combined)
		}
		hashes = nextLevel
	}
	return hashes[0]
}


type MerkleProof struct {
	Hashes   [][]byte // 哈希路径
	Indexes  []bool   // true=右节点，false=左节点
}

// 生成第 index 个叶子的 Merkle 证明
func generateMerkleProof(index int, leaves [][]byte) MerkleProof {
	var proof MerkleProof
	currentIndex := index
	currentLayer := leaves

	for len(currentLayer) > 1 {
		var nextLayer [][]byte
		for i := 0; i < len(currentLayer); i += 2 {
			left := currentLayer[i]
			var right []byte
			if i+1 < len(currentLayer) {
				right = currentLayer[i+1]
			} else {
				right = left // 奇数个节点，复制自己
			}
			parent := hashPair(left, right)
			nextLayer = append(nextLayer, parent)
		}

		// 记录兄弟节点
		siblingIndex := 0
		if currentIndex%2 == 0 {
			// 当前节点在左边
			siblingIndex = currentIndex + 1
			if siblingIndex >= len(currentLayer) {
				siblingIndex = currentIndex // 如果越界则复制自己
			}
			proof.Hashes = append(proof.Hashes, currentLayer[siblingIndex])
			proof.Indexes = append(proof.Indexes, false) // sibling 在右边
		} else {
			// 当前节点在右边
			siblingIndex = currentIndex - 1
			proof.Hashes = append(proof.Hashes, currentLayer[siblingIndex])
			proof.Indexes = append(proof.Indexes, true) // sibling 在左边
		}

		currentIndex /= 2
		currentLayer = nextLayer
	}

	return proof
}


// 使用 Merkle 证明验证叶子是否属于根哈希
func verifyMerkleProof(leaf []byte, proof MerkleProof) []byte {
	hash := leaf
	for i, sibling := range proof.Hashes {
		if proof.Indexes[i] {
			hash = hashPair(sibling, hash) // sibling 在左
		} else {
			hash = hashPair(hash, sibling) // sibling 在右
		}
	}
	return hash
}