Implementation of Shoof's algorithm to find the size of the elliptic curve group

https://en.wikipedia.org/wiki/Schoof%27s_algorithm

Works for finite fields of prime power order not of characteristic 2 and 3

Written in SageMath v. 9.0

to compile from Sage to python, use

`
sage shoof.sage a b q
`

then compiles to shoof.sage.py, which can again be run with

`
python3 shoof.sage.py a b q
`

where q is a prime power not divisible be 2 and 3 and a, b \in F_q are parameters
for elliptic curve in Weierstrass normal form y^2 = x^3 + a*x + b

Works effectively for up to q ~ 500. Possible improvement would be to divide by 
division polynomials throughout the computation. 

Implementation details were taken from A. Drapal's notes Algorithms on Elliptic Curves

https://dl1.cuni.cz/pluginfile.php/1574923/mod_resource/content/1/gralg.pdf
