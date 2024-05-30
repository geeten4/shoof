def shoof_wrapper(q: int, a: int, b: int):
    """
        wrapper for all methods since Sage needs R[x] already defined
        for that we already need to know the value of q.
    """
    R.<x> = GF(q)[]

    class PointMultiplcitaionPolynomials:
        """
            Polynomials describing scalar multiplication in elliptic curve group
            for P = (x, y) it holds
            [m]P = (x - c(m)(x)/d(m)(x), b*r(m)(x)/s(m)(x))
        """

        def __init__(self, a: int, b: int, q: int, division_polynomial):
            self.a = a
            self.b = b
            self.q = q
            self.division_polynomial = division_polynomial

        def c(self, m: int):
            """
                returns numerator of first coordinate of [m]P, (S.1) page 46 in A. Drapal
            """
            # for compatibility with sage, m can be a "modulo integer" which is not further compatible
            m = int(m)

            if m == 1:
                return R(0)

            a = self.a
            b = self.b
            dp = self.division_polynomial

            if m % 2 == 0:
                return dp[m - 1] * dp[m + 1]
            else:
                return 4 * (x^3 + a*x + b) * dp[m - 1] * dp[m + 1]

        def d(self, m: int):
            """
                returns denominator of first coordinate of [m]P, (S.1) page 46 in A. Drapal
            """
            m = int(m)

            if m == 1:
                return R(1)

            a = self.a
            b = self.b
            dp = self.division_polynomial

            if m % 2 == 0:
                return 4 * (x^3 + a*x + b) * dp[m]^2
            else:
                return dp[m]^2

        def r(self, m: int):
            """
                returns numerator of second coordinate of [m]P, (S.2) page 47 in A. Drapal
            """
            m = int(m)

            if m == 1:
                return R(1)

            dp = self.division_polynomial
            return dp[m + 2] * dp[m - 1]^2 - dp[m - 2] * dp[m + 1]^2

        def s(self, m: int):
            """
                returns denominator of second coordinate of [m]P, (S.2) page 47 in A. Drapal
            """
            m = int(m)
            if m == 1:
                return R(1)
            a = self.a
            b = self.b
            dp = self.division_polynomial

            if m % 2 == 0:
                return 16 * (x^3 + a*x + b)^2 * dp[m]^3
            else:
                return dp[m]^3
                
    class DivisionPolynomial:
        """
            recursively generates division polynomials \bar{f_m}, i.e. polynomials s.t.
            for P = (x, y) \in E, then \bar{f_m}(x) = 0 iff P \in E[m] \setminus E[2]
        """

        l = 0  # counts the last polynomial returned
        max_size: int  # maximum number of polynomials that are calculated
        
        def __init__(self, a: int, b: int, q: int):
            """
                a, b: parameters of Weierstrass curve E: y^2 = x^3 + ax + b
                q: power of prime, E is over F_q
            """
            self.a = a
            self.b = b
            self.q = q
            self.max_size = self.q + 1 + 2 * int(n(sqrt(q)) + 1)
            # start with constant polynomials, cannot be of type int for compatibility
            self._polynomials = [R(0), R(1), R(1)]
            self._polynomials.append(3*x^4 + 6*a*x^2 + 12*b*x - a^2)
            self._polynomials.append(2*(x^6 + 5*a*x^4 + 20*b*x^3 - 5*a^2*x^2 - 4*a*b*x - 8*b^2 - a^3))
            self.calc_all()
            
        def third(self):
            self.l = 2
            return self.next()

        def next(self):
            self.l += 1
            # handle base cases
            if self.l < len(self._polynomials):
                return self._polynomials[self.l]

            m = self.l // 2
            ps = self._polynomials

            # page 38 in A. Drapal scripts
            if self.l % 2 == 0:
                # l is even
                new_f = ps[m] * (ps[m + 2] * ps[m - 1]^2 - ps[m-2] * ps[m + 1]^2)
                self._polynomials.append(new_f)
                return new_f

            g = x^3 + self.a * x + self.b

            # l is odd
            if m % 2 == 0:
                # m is even            
                new_f = 16 * g^2 * ps[m + 2] * ps[m]^3 - ps[m - 1] * ps[m + 1]^3
            else:
                # m is odd
                new_f = ps[m + 2] * ps[m]^3 - 16*g^2 * ps[m - 1] * ps[m + 1]^3

            self._polynomials.append(new_f)
            return new_f

        def calc_all(self):
            for i in range(self.max_size):
                self.next()

        def get_nth(self, n: int):
            n = int(n)
            if n < 0:
                raise ValueError(f'Negative integer division polynomial: {n}')
            return self._polynomials[n]

        def __getitem__(self, key: int):
            key = int(key)
            return self.get_nth(key)

    class FirstCoordinatePolynomial:
        """
            calculates polynomials \bar{s}_m, where \bar{s}_m(\alpha) = 0 iff
            iff exists \beta s.t. P = (\alpha, \beta), \varphi^2(P) = [+-m]P
        """

        def __init__(self, a: int, b: int, q: int, division_polynomial):
            self.a = a
            self.b = b
            self.q = q
            self.division_polynomial = division_polynomial
        
        def get_nth(self, m: int):
            q = self.q
            a = self.a
            b = self.b
            dp = self.division_polynomial

            g = x^(q^2) - x
            h = x^3 + a*x + b
            if m == 1:
                return g
            elif m % 2 == 0:
                return 4 * g * h * dp[m]^2 + dp[m - 1] * dp[m + 1]
            else:
                return g * dp[m]^2 + 4 * h * dp[m - 1] * dp[m + 1]

        def __getitem__(self, key: int):
            return self.get_nth(key)

    def equalx(g_l, a: int, b: int, q: int, l: int, division_polynomial):
        """
            returns t_l assuming there exists a P s.t. the first coordinates of \varphi^2(P) and [q_l]P agree.
        """
        q_l = q % l
        if tyzero(a=a, b=b, q=q, l=l, m=q_l, division_polynomial=division_polynomial):
            # since \varphi^2(P) = [-q_l]P, then t_l = 0
            return 0

        # compare [q_l]P with [sqrt(q_l)]\varphi(P), if they are equal, then
        # t_l = 2*sqrt(q_l), else t_l = -2*sqrt(q_l)
        tau = sqrt_mod(4*q_l, l)
        gamma = 2 * q_l * invert_mod(tau, l) % l

        if eigen(g_l, a=a, b=b, q=q, l=l, m=gamma, division_polynomial=division_polynomial):
            return tau
        else:
            return -tau % l

    def tyzero(a: int, b: int, q: int, l: int, m: int, division_polynomial):
        """
            returns True if there exists P = (\alpha, \beta) s.t. P \in E[l]*,
            \varphi^2(P) = [-m]P, assuming there exists a P for which the
            first coordinates of \varphi^2(P) and [-m]P agree.
        """
        dp = division_polynomial
        pmp = PointMultiplcitaionPolynomials(a, b, q, dp)
        r_m = pmp.r(m)
        s_m = pmp.s(m)

        g = s_m * (x^3 + a*x + b)^((q^2 - 1) // 2) + r_m
        quo, rem = g.quo_rem(dp[l])
        return rem == 0

    def eigen(g_l, a: int, b: int, q: int, l: int, m: int, division_polynomial):
        """
            returns True if there exists a P \in E[l]* s.t. \varphi(P) = [m]P
        """

        pmp = PointMultiplcitaionPolynomials(a, b, q, division_polynomial)
        c_m = pmp.c(m)
        d_m = pmp.d(m)
        r_m = pmp.r(m)
        s_m = pmp.s(m)

        fc = (x^q - x) * d_m + c_m  # first coordinate equality
        sc = (x^3 + a*x + b)^((q - 1) // 2) * s_m - r_m  # second coordinate equality
        return gcd([g_l, sc, fc]) != 1

    def sqrt_mod(a: int, l: int):
        """
            returns sqrt(a) (mod l) and asserts the square root exists
        """
        R.<y> = GF(l)[]
        g = y^2 - a
        assert g.roots() != []
        return g.roots()[0][0]

    def invert_mod(a: int, l: int):
        """
            returns a^-1 (mod l)
        """
        if a == 0:
            raise ValueError("Cannot divide by zero.")
        R.<z> = GF(l)[]
        g = a*z - 1
        return g.roots()[0][0]

    def nonequalx(a: int, b: int, q: int, l: int, tau: int, division_polynomial):
        """
            Assume for a prime l \varphi^2(P) and [q_l]P differ in x coordinates
            for all P \in E[l]*
            input tau < l / 2 being a candidate for t_l

            returns 0 if t_l != +- tau
            returns 1 if t_l == tau
            returns -1 if t_l == -tau
        """
        dp = division_polynomial
        h_x = h_X(a, b, q, l, tau, dp)
        if gcd(h_x, dp[l]) == 1:
            return 0

        h_y = h_Y(a, b, q, l, tau, dp)
        if gcd(h_y, dp[l]) == 1:
            return -1

        return 1

    def h_X(a: int, b: int, q: int, l: int, tau: int, division_polynomial):
        # compute h_X comparing x-coordinates of \varphi^2(P) + [q_l]P with [tau]P
        
        m = q % l
        pmp = PointMultiplcitaionPolynomials(a, b, q, division_polynomial)
        r_m = pmp.r(m)
        s_m = pmp.s(m)
        c_m = pmp.c(m)
        d_m = pmp.d(m)
        # lambda^2 = \beta^2 * lambda_bar^2
        lambda_bar_numerator = d_m * ((x^3 + a*x + b)^((q^2 - 1) // 2) * s_m - r_m)
        lambda_bar_denom = s_m * (d_m * (x^(q^2) - x) + c_m)

        d_tau_q = pmp.d(tau)(x^q)
        c_tau_q = pmp.c(tau)(x^q)

        g = (x^3 + a*x + b)*lambda_bar_numerator^2*d_m*d_tau_q
        f = lambda_bar_denom^2 * (-(x^(q^2) + x^q + x) * d_m * d_tau_q + c_m*d_tau_q + c_tau_q*d_m)
        return g + f

    def h_Y(a: int, b: int, q: int, l: int, tau: int, division_polynomial):
        # compute h_Y comparing y-coordinates of \varphi^2(P) + [q_l]P with [tau]P
        m = q % l
        pmp = PointMultiplcitaionPolynomials(a, b, q, division_polynomial)
        r_m = pmp.r(m)
        s_m = pmp.s(m)
        c_m = pmp.c(m)
        d_m = pmp.d(m)
        # lambda^2 = \beta^2 * lambda_bar^2
        lambda_bar_numerator = d_m * ((x^3 + a*x + b)^((q^2 - 1) // 2) * s_m - r_m)
        lambda_bar_denom = s_m * (d_m * (x^(q^2) - x) + c_m)

        r_tau_q = pmp.r(tau)(x^q)
        s_tau_q = pmp.s(tau)(x^q)

        f = x^3 + a*x + b
        LHS = f^((q-1)//2) * r_tau_q * d_m * lambda_bar_denom^3
        RHS1 = -s_tau_q * d_m * lambda_bar_numerator^3 * f
        RHS2 = s_tau_q * d_m * lambda_bar_numerator * (2*x^(q^2) + x) * lambda_bar_denom^2
        RHS3 = -lambda_bar_numerator * c_m * s_tau_q * lambda_bar_denom^2
        RHS4 = -f^((q^2 - 1)//2) * s_tau_q * d_m * lambda_bar_denom^3
        
        return LHS - RHS1 - RHS2 - RHS3 - RHS4

    def shoof(q: int, a: int, b: int) -> int:
        """
            Shoofs algorithm
            
            @input
                q: power of a prime p
                a, b \in GF(q): determine a smooth Weierstrass curve E: y^2 = x^3 + ax + b
            
            @output
                |E(GF(q))| i.e. order of the abelian group on E
                |E(GF(q))| = q + 1 - t
        """

        if (4*a^3 + 27*b^2) % q == 0:
            raise ValueError('Singular curve.')
        
        primes = Primes()
        l = primes.first()  # small prime, begins at 2
        B = 2  # product of primes in l
        M: set[tuple[int, int]] = set()  # set of tuples (l, t_l), t_l = t (mod l)

        # first check for involutions
        if gcd(x^q - x, x^3 + a*x + b) == 1:
            # no element of the finite field is an involution
            M.add((2, 1))
        else:
            M.add((2,0))

        dp = DivisionPolynomial(a, b, q)
        fcp = FirstCoordinatePolynomial(a, b, q, dp)
        while B < 4*n(sqrt(q)):
            l = primes.next(l)
            q_l = q % l
            if q_l == 0:
                # skip primes that divide q
                continue

            B *= l

            g_l = gcd(dp[l], fcp[q_l])
            if g_l != 1:
                # now there exists a P s.t. P \in E[l]* \ E[2]* and the first coordinates of
                # \varphi^2(P) and [q_l]P agree.
                tau = equalx(g_l, a=a, b=b, q=q, l=l, division_polynomial=dp)
            else:
                tau = 0
                r = 0
                while r == 0:
                    tau += 1
                    r = nonequalx(a, b, q, l, tau, dp)

                if r == -1:
                    tau = -tau % l

            M.add((l, tau))
        
        # recover t using all l's, t_l's and CRT
        # here CRT returns t in the interval 0 <= t <= B <= 4*sqrt(q)
        # so if by Hasse t > 2*sqrt(q), subtract B and it must be negative,
        # not chaning the CRT outcome
        t = int(CRT([int(t_l) for (l, t_l) in M], [int(l) for (l, t_l) in M]))
        if t > 2*n(sqrt(q)):
            t = t - B

        return q + 1 - t

    return shoof(q, a, b)


# get sys arguments
a, b, q = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])

if len(factor(q)) > 1:
    raise ValueError(f"{q} is not a power of a prime.")

# validate for tests
size = shoof_wrapper(q, a, b)
assert EllipticCurve(GF(q), [a,b]).cardinality() == size

print(f"Size of E(F_{q}) for E: y^2 = x^3 + {a}*x + {b} is {size}")
