package main

import (
	"crypto/rand"
	"fmt"
	"math/big"
)

func isPrime(number *big.Int) bool {
	if number.Cmp(big.NewInt(2)) == 0 {
		return false
	}
	i := big.NewInt(2)
	result := new(big.Int)
	firstTmp, secondTmp := new(big.Int), new(big.Int)
	for i.Cmp(result.Add(number, big.NewInt(1))) == -1 {
		firstTmp.Add(number, big.NewInt(1))
		secondTmp.Mul(i, i)
		var check bool
		check = secondTmp.Cmp(firstTmp) == -1
		secondTmp.Mod(number, i)
		check = check && secondTmp.Cmp(big.NewInt(0)) == 0
		if check {
			return false
		}
		i.Add(i, big.NewInt(1))
	}
	return true
}

func pollardFactorize(number *big.Int) *big.Int {
	x, tmp := new(big.Int), new(big.Int)
	var cmpResult int
	x, err := rand.Int(rand.Reader, tmp.Sub(number, big.NewInt(2)))
	if err != nil {
		panic(err)
	}
	y, i, stage := big.NewInt(1), big.NewInt(0), big.NewInt(2)
	tmp.GCD(nil, nil, number, tmp.Abs(tmp.Sub(x, y)))
	cmpResult = tmp.Cmp(big.NewInt(1))
	for cmpResult == 0 {
		if i.Cmp(stage) == 0 {
			*y = *x
			stage.Mul(stage, big.NewInt(2))
		}
		*x = *tmp.Mod(tmp.Add(tmp.Mul(x, x), big.NewInt(1)), number)
		i.Add(i, big.NewInt(1))
		tmp.GCD(nil, nil, number, tmp.Abs(tmp.Sub(x, y)))
		cmpResult = tmp.Cmp(big.NewInt(1))
		if i.Cmp(big.NewInt(100000)) == 0 {
			tmp = pollardFactorize(number)
			return tmp
		}
	}
	return tmp
}

func computeEulerFunction(enteredNumber *big.Int) *big.Int {
	result, i, p, firstTmp, secondTmp, number, n := big.NewInt(1), big.NewInt(2), new(big.Int),
		new(big.Int), new(big.Int), new(big.Int), new(big.Int)
	number.Add(enteredNumber, big.NewInt(0))
	firstTmp.Mul(i, i)
	for firstTmp.Cmp(secondTmp.Add(number, big.NewInt(1))) == -1 {
		*p = *big.NewInt(1)
		*firstTmp = *big.NewInt(0)
		for firstTmp.Cmp(secondTmp.Mod(number, i)) == 0 {
			number.Div(number, i)
			p.Mul(p, i)
		}
		p.Div(p, i)
		if p.Cmp(big.NewInt(0)) != 0 {
			result.Mul(result, firstTmp.Mul(p, secondTmp.Sub(i, big.NewInt(1))))
		}
		i.Add(i, big.NewInt(1))
	}
	n.Sub(number, big.NewInt(1))
	if n.Cmp(big.NewInt(0)) == 0 {
		return result
	} else {
		return secondTmp.Mul(n, result)
	}
}

func pollardSolve(a, b, p *big.Int) *big.Int {
	n := computeEulerFunction(p)
	if a.Cmp(b) == 0 {
		return big.NewInt(1)
	}
	a1, a2, b1, b2, x1, x2, u, v, tmp, d, nu := big.NewInt(0), big.NewInt(0), big.NewInt(0),
		big.NewInt(0), big.NewInt(1), big.NewInt(1),
		new(big.Int), new(big.Int), new(big.Int),
		new(big.Int), new(big.Int)
	start := true
	for x1.Cmp(x2) != 0 || start {
		start = false
		if x1.Cmp(tmp.Div(p, big.NewInt(3))) == -1 {
			x1.Mod(tmp.Mul(b, x1), p)
			b1.Mod(tmp.Add(b1, big.NewInt(1)), n)
		} else if (x1.Cmp(tmp.Div(p, big.NewInt(3))) == 0 ||
			x1.Cmp(tmp.Div(p, big.NewInt(3))) == 1) &&
			x1.Cmp(tmp.Mul(tmp.Div(p, big.NewInt(3)), big.NewInt(2))) == -1 {
			x1.Mod(tmp.Mul(x1, x1), p)
			a1.Mod(tmp.Mul(big.NewInt(2), a1), n)
			b1.Mod(tmp.Mul(big.NewInt(2), b1), n)
		} else {
			x1.Mod(tmp.Mul(a, x1), p)
			a1.Mod(tmp.Add(a1, big.NewInt(1)), n)
		}
		for i := 0; i < 2; i++ {
			if x2.Cmp(tmp.Div(p, big.NewInt(3))) == -1 {
				x2.Mod(tmp.Mul(b, x2), p)
				b2.Mod(tmp.Add(b2, big.NewInt(1)), n)
			} else if (x2.Cmp(tmp.Div(p, big.NewInt(3))) == 0 ||
				x2.Cmp(tmp.Div(p, big.NewInt(3))) == 1) &&
				x2.Cmp(tmp.Mul(tmp.Div(p, big.NewInt(3)), big.NewInt(2))) == -1 {
				x2.Mod(tmp.Mul(x2, x2), p)
				a2.Mod(tmp.Mul(big.NewInt(2), a2), n)
				b2.Mod(tmp.Mul(big.NewInt(2), b2), n)
			} else {
				x2.Mod(tmp.Mul(a, x2), p)
				a2.Mod(tmp.Add(a2, big.NewInt(1)), n)
			}
		}
	}
	u.Mod(tmp.Sub(a1, a2), n)
	v.Mod(tmp.Sub(b2, b1), n)
	if tmp.Mod(v, n).Cmp(big.NewInt(0)) == 0 {
		return nil
	}
	d.GCD(nu, nil, v, n)
	x, i, w, firstTmp, secondTmp := new(big.Int), big.NewInt(0), new(big.Int), tmp, new(big.Int)
	for i.Cmp(tmp.Add(d, big.NewInt(1))) != 0 {
		*w = *i
		firstTmp.Mul(u, nu)
		secondTmp.Mul(w, n)
		secondTmp.Add(firstTmp, secondTmp)
		secondTmp.Div(secondTmp, d)
		x.Mod(secondTmp, n)
		secondTmp.Exp(a, x, big.NewInt(0))
		secondTmp.Sub(secondTmp, b)
		tmp.Mod(secondTmp, p)
		if tmp.Cmp(big.NewInt(0)) == 0 {
			return x
		}
		i.Add(i, big.NewInt(1))
	}
	return nil
}

func computeMobiusFunction(enteredNumber *big.Int) int {
	p, tmp, number, square := new(big.Int), new(big.Int), new(big.Int), new(big.Int)
	number.Add(enteredNumber, big.NewInt(0))
	if tmp.Mod(number, big.NewInt(2)).Cmp(big.NewInt(0)) == 0 {
		number.Div(number, big.NewInt(2))
		p.Add(p, big.NewInt(1))
		if tmp.Mod(number, big.NewInt(2)).Cmp(big.NewInt(0)) == 0 {
			return 0
		}
	}
	square.Sqrt(number)
	for i := big.NewInt(3); i.Cmp(square) == -1; i.Add(i, big.NewInt(2)) {
		if tmp.Mod(number, i).Cmp(big.NewInt(0)) == 0 {
			number.Div(number, i)
			p.Add(p, big.NewInt(1))
			if tmp.Mod(number, i).Cmp(big.NewInt(0)) == 0 {
				return 0
			}
		}
	}
	if tmp.Mod(p, big.NewInt(2)).Cmp(big.NewInt(0)) == 0 {
		return -1
	} else {
		return 1
	}
}

func computeLegendreSymbol(enteredA, enteredN *big.Int) int {
	if !isPrime(enteredN) {
		panic("Legendre's symbol for product (a/n), where n is not prime number, is undefined")
	}
	return computeJacobiSymbol(enteredA, enteredN)
}

func computeJacobiSymbol(enteredA, enteredN *big.Int) int {
	t := 1
	tmp, a, n, r := new(big.Int), new(big.Int), new(big.Int), new(big.Int)
	a.Add(enteredA, big.NewInt(0))
	n.Add(enteredN, big.NewInt(0))
	if n.Cmp(big.NewInt(0)) != 1 {
		panic("Jacobi symbol for product (a/n), where n <= 0, is undefined")
	}
	if tmp.Mod(n, big.NewInt(2)).Cmp(big.NewInt(1)) != 0 {
		panic("Jacobi symbol for product (a/n), where n is even number, is undefined")
	}
	a.Mod(a, n)
	for a.Cmp(big.NewInt(0)) != 0 {
		for tmp.Mod(a, big.NewInt(2)).Cmp(big.NewInt(0)) == 0 {
			a.Rsh(a, 1)
			r.Mod(n, big.NewInt(8))
			if r.Cmp(big.NewInt(3)) == 0 || r.Cmp(big.NewInt(5)) == 0 {
				t *= -1
			}
		}
		r.Add(n, big.NewInt(0))
		n.Add(a, big.NewInt(0))
		a.Add(r, big.NewInt(0))
		if tmp.Mod(a, big.NewInt(4)).Cmp(big.NewInt(3)) == 0 &&
			tmp.Mod(n, big.NewInt(4)).Cmp(big.NewInt(3)) == 0 {
			t *= -1
		}
		a.Mod(a, n)
	}
	if n.Cmp(big.NewInt(1)) == 0 {
		return t
	} else {
		return 0
	}
}

func cipollaSolve(n, p *big.Int) (*big.Int, *big.Int) {
	tmp := new(big.Int)
	powModP := func(a, e *big.Int) *big.Int {
		s := big.NewInt(1)
		for ; e.Cmp(big.NewInt(0)) == 1; e.Sub(e, big.NewInt(1)) {
			s.Mod(s.Mul(s, a), p)
		}
		return s
	}
	ls := func(a *big.Int) *big.Int {
		return powModP(a, tmp.Div(tmp.Sub(p, big.NewInt(1)), big.NewInt(2)))
	}
	if ls(n).Cmp(big.NewInt(1)) != 0 {
		return nil, nil
	}
	a, w2, tmp := new(big.Int), new(big.Int), new(big.Int)
	for a = big.NewInt(0); ; a.Add(a, big.NewInt(1)) {
		tmp.Mul(a, a)
		tmp.Add(tmp, p)
		tmp.Sub(tmp, n)
		w2.Mod(tmp, p)
		if ls(w2).Cmp(tmp.Sub(p, big.NewInt(1))) == 0 {
			break
		}
	}
	type point struct{ x, y *big.Int }
	mul := func(a, b point) point {
		x, y, firstTmp, secondTmp := new(big.Int), new(big.Int), new(big.Int), new(big.Int)
		firstTmp.Mul(a.x, b.x)
		secondTmp.Mul(a.y, b.y)
		secondTmp.Mul(secondTmp, w2)
		secondTmp.Add(firstTmp, secondTmp)
		x.Mod(secondTmp, p)
		firstTmp.Mul(a.x, b.y)
		secondTmp.Mul(b.x, a.y)
		secondTmp.Add(firstTmp, secondTmp)
		y.Mod(secondTmp, p)
		return point{x, y}
	}
	r := point{big.NewInt(1), big.NewInt(0)}
	s := point{a, big.NewInt(1)}
	tmp.Add(p, big.NewInt(1))
	tmp.Rsh(tmp, 1)
	i := new(big.Int)
	i.Mod(tmp, p)
	for ; i.Cmp(big.NewInt(0)) == 1; i.Rsh(i, 1) {
		if tmp.And(i, big.NewInt(1)).Cmp(big.NewInt(1)) == 0 {
			r = mul(r, s)
		}
		s = mul(s, s)
	}
	if r.y.Cmp(big.NewInt(0)) != 0 {
		return nil, nil
	}
	if tmp.Mod(tmp.Mul(r.x, r.x), p).Cmp(n) != 0 {
		return nil, nil
	}
	return r.x, tmp.Sub(p, r.x)
}

func main() {
	wish := true
	var answer string
	for wish {
		fmt.Print("List of algorithms:\n" +
			"1: Pollard's factorization\n" +
			"2: Pollard's solving of discrete logarithm problem\n" +
			"3: Computing of Euler's function\n" +
			"4: Computing of Mobius's function\n" +
			"5: Computing of Legendre's symbol\n" +
			"6: Computing of Jacobi's symbol\n" +
			"7: Cipolla's algorithm of finding of discrete square root\n" +
			"Which of algorithms would you like to use?\n")
		var choice string
		_, err := fmt.Scan(&choice)
		if err != nil {
			panic(err)
		}
		switch choice {
		case "1":
			{
				fmt.Println("Enter number to factorize:")
				number := new(big.Int)
				var enteredNumber string
				_, err = fmt.Scan(&enteredNumber)
				if err != nil {
					panic(err)
				}
				number.SetString(enteredNumber, 10)
				var divider *big.Int
				if isPrime(number) {
					fmt.Println(number, "has no dividers")
				} else {
					divider = pollardFactorize(number)
					fmt.Print(number, " = ", divider, "*")
					number.Div(number, divider)
					for !isPrime(number) {
						divider = pollardFactorize(number)
						fmt.Print(divider, "*")
						number.Div(number, divider)
					}
					fmt.Println(number)
				}
			}
		case "2":
			{
				fmt.Println("Enter parameters of equation a^x = b (mod p):")
				var enteredA, enteredB, enteredP string
				fmt.Print("a: ")
				_, err = fmt.Scan(&enteredA)
				if err != nil {
					panic(err)
				}
				fmt.Print("b: ")
				_, err = fmt.Scan(&enteredB)
				if err != nil {
					panic(err)
				}
				fmt.Print("p: ")
				_, err = fmt.Scan(&enteredP)
				if err != nil {
					panic(err)
				}
				a, b, p := new(big.Int), new(big.Int), new(big.Int)
				a.SetString(enteredA, 10)
				b.SetString(enteredB, 10)
				p.SetString(enteredP, 10)
				x := pollardSolve(a, b, p)
				if x != nil {
					fmt.Print("Root of equation ", a, "^x = ", b, " (mod ", p, ") is x = ", x, "\n")
				} else {
					fmt.Print("Equation ", a, "^x = ", b, " (mod ", p, ") has no root\n")
				}
			}
		case "3":
			{
				fmt.Println("Enter number:")
				number := new(big.Int)
				var enteredNumber string
				_, err = fmt.Scan(&enteredNumber)
				if err != nil {
					panic(err)
				}
				number.SetString(enteredNumber, 10)
				result := computeEulerFunction(number)
				fmt.Println("Result of computing Euler's function for number", number, "is", result)
			}
		case "4":
			{
				fmt.Println("Enter number:")
				number := new(big.Int)
				var enteredNumber string
				_, err = fmt.Scan(&enteredNumber)
				if err != nil {
					panic(err)
				}
				number.SetString(enteredNumber, 10)
				result := computeMobiusFunction(number)
				fmt.Println("Result of computing Mobius's function for number", number, "is", result)
			}
		case "5":
			{
				fmt.Println("Enter parameters of product (a/n):")
				var enteredA, enteredN string
				fmt.Print("a: ")
				_, err = fmt.Scan(&enteredA)
				if err != nil {
					panic(err)
				}
				fmt.Print("n: ")
				_, err = fmt.Scan(&enteredN)
				if err != nil {
					panic(err)
				}
				a, n := new(big.Int), new(big.Int)
				a.SetString(enteredA, 10)
				n.SetString(enteredN, 10)
				result := computeLegendreSymbol(a, n)
				fmt.Print("Result of computing Legendre's symbol for product (", a,
					"/", n, ") is ", result, "\n")
			}
		case "6":
			{
				fmt.Println("Enter parameters of product (a/n):")
				var enteredA, enteredN string
				fmt.Print("a: ")
				_, err = fmt.Scan(&enteredA)
				if err != nil {
					panic(err)
				}
				fmt.Print("n: ")
				_, err = fmt.Scan(&enteredN)
				if err != nil {
					panic(err)
				}
				a, n := new(big.Int), new(big.Int)
				a.SetString(enteredA, 10)
				n.SetString(enteredN, 10)
				result := computeJacobiSymbol(a, n)
				fmt.Print("Result of computing Jacobi's symbol for product (", a,
					"/", n, ") is ", result, "\n")
			}
		case "7":
			{
				fmt.Println("Enter parameters of equation x^2 = n (mod p):")
				var enteredN, enteredP string
				fmt.Print("n: ")
				_, err = fmt.Scan(&enteredN)
				if err != nil {
					panic(err)
				}
				fmt.Print("p: ")
				_, err = fmt.Scan(&enteredP)
				if err != nil {
					panic(err)
				}
				n, p := new(big.Int), new(big.Int)
				n.SetString(enteredN, 10)
				p.SetString(enteredP, 10)
				x1, x2 := cipollaSolve(n, p)
				if x2 != nil {
					fmt.Print("Roots of equation x^2 = ", n, " (mod ", p, ") are ", x1,
						" and ", x2, "\n")
				} else {
					fmt.Print("Equation x^2 = ", n, " (mod ",
						p, ") may not be solved by Cipolla's algorithm\n")
				}
			}
		}
		fmt.Println("Enter \"More\" if you would like to continue using of algorithms, otherwise " +
			"enter anything else")
		_, err = fmt.Scan(&answer)
		if err != nil {
			panic(err)
		}
		if answer != "More" {
			wish = false
		}
	}
}
