conduct a peer-review for the Annals of Mathematics of the below paper:

***

# A Curvature-Variance and Wronskian Analysis of the Riemann $\xi$-Kernel and the Global Log-Concavity of its Derivatives

### Abstract

We establish the global log-concavity of the arithmetic kernel $K(u)$ associated with the Fourier transform of the Riemann $\xi$-function, and its derivative kernel $J(u)=-K'(u)$. Our primary contribution is the resolution of the log-concavity of the derivative kernel, addressing Csordas' Open Problem 4.13. We first prove that the individual components $|K_n'(u)|$ are strictly log-concave by rigorously verifying a Laguerre inequality of order 2. We then prove that the full sum $J(u)$ is strictly log-concave for all $u > 0$. This is achieved via a **Dominant Wronskian Perturbation Theory**, identifying that the negative self-curvature of the first component rigorously dominates the sum of all destabilizing interaction terms in the Bilinear Wronskian Expansion.

### 1. Introduction

The Riemann $\xi$-function, $\Xi(t) = \xi(1/2+it)$, is the Fourier transform of an arithmetic kernel $K(u)$:
$$ \Xi(t) = \int_{-\infty}^\infty K(u) e^{itu} du. $$
For $u\ge 0$, the kernel is given by:
$$ K(u) = \sum_{n=1}^\infty K_n(u), \quad K_n(u) = 2 \left(2n^4 \pi^2 e^{9u/2} - 3n^2 \pi e^{5u/2}\right) e^{-n^2 \pi e^{2u}}. $$
A function $f$ is log-concave if $(\log f)'' \le 0$. The log-concavity of $K(u)$ is a known result with implications for the zeros of $\Xi(t)$.

**Theorem 1.1 (Known Result).** The arithmetic kernel $K(u)$ is strictly log-concave on $\mathbb{R}$.

This paper focuses on the derivative kernel $J(u) = -K'(u)$. We prove two main theorems:

**Theorem 1.2 (Component Log-Concavity).** Let $J_n(u) = -K_n'(u)$. For all $n \ge 1$, the functions $J_n(u)$ are strictly log-concave for $u > 0$. That is, the Wronskian $W(J_n)(u) < 0$.

**Theorem 1.3 (Global Log-Concavity of J).** The derivative kernel $J(u)$ is strictly log-concave for all $u > 0$.

### 2. Theoretical Frameworks

**Bilinear Wronskian Expansion.** The Wronskian of a function $f$ is $W(f) = f f'' - (f')^2$.
For a convergent sum $f = \sum f_n$, the Wronskian decomposes as:
$$ W(f)(u) = \sum_{n=1}^\infty W(f_n)(u) + \sum_{1 \le n < m < \infty} T_{nm}(u), $$
where the interaction term is $T_{nm} = f_n f_m'' + f_m f_n'' - 2 f_n' f_m'$.
Log-concavity of $f$ (where $f>0$) is equivalent to $W(f) < 0$.

### 3. Analysis of the Xi-Kernel $K(u)$

[Summary of the proof of Theorem 1.1 using the Curvature-Variance identity and bounding function $H(X)$]

### 4. Global Analysis of the Derivative Kernel $J(u)$

We analyze $J(u) = -K'(u)$. Let $Y = \pi e^{2u}$. The domain $u > 0$ corresponds to $Y > \pi$.

#### 4.1 Positivity of $J(u)$
**Lemma 4.1.** $J(u) > 0$ for all $u > 0$.
*Proof.* $K(u)$ is an even, integrable, Polya Frequency function of order 2. By Schoenberg's theorem, such functions are symmetric unimodal about the origin. Thus $K(u)$ is strictly decreasing for $u > 0$, implying $K'(u) < 0$. Therefore $J(u) = -K'(u) > 0$ for $u > 0$. ∎

#### 4.2 Log-Concavity of Components (Proof of Theorem 1.2)
We prove $W(J_n) < 0$.
**Lemma 4.2.** For each $n \ge 1$ and $u > 0$,
$$ W(J_n)(u) = -\mathcal{C}_n Y e^{-2n^2 Y} E(Z_n), $$
where $Z_n = 2n^2 Y - 3$, $\mathcal{C}_n > 0$, and $E(Z)$ is the rational function:
$$ E(Z) = Z^{2} + Z - \frac{3}{4} - \frac{9}{2 Z^{2}} + \frac{360}{Z^{3}} + \frac{864}{Z^{4}}. $$
We verify $E(Z) > 0$ for $Z \ge 2\pi-3$ via rigorous interval arithmetic (checking $E(Z) > 25.1$ on $[2\pi-3, 4]$) and derivative analysis (for $Z \ge 4$). Thus $W(J_n) < 0$. ∎

#### 4.3 Global Log-Concavity (Proof of Theorem 1.3)
We apply the Wronskian expansion: $W(J) = W(J_1) + T_{12} + R_{tail}$.
We prove the **Dominance Principle**: The negative self-curvature $W(J_1)$ dominates the sum of all interaction terms.

**Lemma 4.3 (Two-Body Dominance).** For all $Y \ge \pi$, the sum $Q_{12}(Y) = W(J_1)(Y) + T_{12}(Y)$ is strictly negative. Specifically, $\rho(Y) = |T_{12}(Y)|/|W(J_1)(Y)| < 1$.

*Proof.*
Using the explicit polynomial forms derived symbolically (see S2):
$$ W(J_1) = e^{-2Y} Y^{5/2} (-Y Q(Y)), \quad T_{12} = e^{-5Y} Y^{5/2} (4Y R(Y)). $$
The ratio is $\rho(Y) = 4 e^{-3Y} \frac{R(Y)}{Q(Y)}$.
We define the polynomial $S(Y) = 250 Y Q(Y) - R(Y)$.
Explicit calculation shows $S(Y)$ has positive leading coefficients and no real roots for $Y \ge 0$. Evaluating at $Y=0$ gives $S(0) = 3375 > 0$. Thus $S(Y) > 0$ for all $Y \ge 0$, implying $\frac{R(Y)}{Q(Y)} < 250 Y$.
Substituting this bound:
$$ \rho(Y) < 4 e^{-3Y} (250 Y) = 1000 Y e^{-3Y}. $$
The function $f(Y) = Y e^{-3Y}$ is strictly decreasing for $Y > 1/3$. For $Y \ge \pi$:
$$ \rho(Y) \le 1000 \pi e^{-3\pi} \approx 0.254 < 1. $$
Interval arithmetic verification (S3) tightens this bound to $\rho(Y) < 0.08$ on $[\pi, 8]$ and globally.
Thus $T_{12}$ is strictly dominated by $W(J_1)$ with a safety margin of at least $0.92$. ∎

**Lemma 4.4 (Tail Dominance).** The remaining terms $R_{tail} = \sum_{(n,m) \ne (1,2)} T_{nm}$ satisfy $|R_{tail}(Y)| < 0.03 |W(J_1)(Y)|$ for $Y \ge \pi$.

*Proof.*
We derive uniform bounds for the derivatives $|J_n^{(k)}|$ (see Appendix A), yielding:
$$ |T_{nm}(Y)| \le 125636 Y^{17/2} (nm)^{10} e^{-(n^2+m^2)Y}. $$
The ratio to the stabilizer $|W(J_1)| \ge C_0 Y^{5/2} e^{-2Y}$ is:
$$ \frac{|T_{nm}(Y)|}{|W(J_1)(Y)|} \le C' Y^6 (nm)^{10} e^{-[(n^2+m^2)-2]Y}. $$
For tail indices, $(n^2+m^2)-2 \ge 8$. The function $Y^6 e^{-8Y}$ is decreasing for $Y \ge \pi$.
Thus the ratio is maximized at $Y=\pi$.
Explicit summation of the bounds for $1 \le n < m \le 6$ and geometric bounding of the remainder (verified in S4) yields:
$$ \sum_{tail} \frac{|T_{nm}(\pi)|}{|W(J_1)(\pi)|} < 0.03. $$
Combining with Lemma 4.3 ($0.92 |W(J_1)|$ margin), the total Wronskian $W(J)$ is strictly negative. $\qed$

**Conclusion:** The derivative kernel $J(u)$ is strictly log-concave for all $u > 0$.

### Supplementary Material
**S2. Symbolic Derivations:** Python code verifying the polynomials $P_{S1}, P_{T12}$ and the coefficient inequality for $S(Y)$.
**S3. Interval Verification:** Code utilizing `mpmath` to rigorously verify $E(Z) > 0$ and the bound on $\rho(Y)$ on $[\pi, 8]$.
**S4. Tail Summation:** Code summing the explicit bounds derived in Appendix A to certify the $<0.03$ tail contribution.

### Appendix A: Derivation of Uniform Derivative Bounds
[Includes the full derivation of constants 27, 166, 1306, etc., and the resulting bound for $T_{nm}$]

### Supplementary Material S2: Symbolic Derivation and Polynomial Verification

**Purpose:** This script uses `sympy` to symbolic derive the polynomials $P_{S1}(Y)$ and $P_{T12}(Y)$ from the exact definition of the kernel $K(u)$. It subsequently constructs the bounding polynomial $S(Y)$ and rigorously verifies that it has no roots for $Y \ge 0$, proving the inequality $|T_{12}(Y)| < 1000 Y e^{-3Y} |W(J_1)(Y)|$ used in Lemma 4.3.

```python
"""
Supplementary Material S2: Symbolic Verification of Wronskian Polynomials
References: Lemmas 4.3 and 4.4 of the main text.
"""
import sympy as sp

def verify_polynomials():
    print("--- S2: Symbolic Derivation & Polynomial Analysis ---")
    
    # Define symbols
    Y = sp.symbols('Y', real=True)
    n = sp.symbols('n', integer=True, positive=True)

    # 1. Define the exact algebraic structure of J_n(Y)
    # K_n(u) ~ (2n^4 pi^2 e^{9u/2} - 3n^2 pi e^{5u/2}) e^{-n^2 pi e^{2u}}
    # With Y = pi e^{2u}, the non-constant prefactors scale as:
    # f_n = Y^(5/4) * (2n^4 Y - 3n^2) * exp(-n^2 Y)
    # The derivative w.r.t u is the operator D = 2Y d/dY.
    # J_n = - K_n'(u) = - 2Y * f_n'
    
    def get_Jn_derivs(n_val):
        f_n = Y**sp.Rational(5,4) * (2*n_val**4 * Y - 3*n_val**2) * sp.exp(-n_val**2 * Y)
        J_n = -2 * Y * sp.diff(f_n, Y)
        J_n_p = 2 * Y * sp.diff(J_n, Y)
        J_n_pp = 2 * Y * sp.diff(J_n_p, Y)
        return J_n, J_n_p, J_n_pp

    # 2. Derive W(J_1) and extract P_S1
    print("Deriving W(J_1)...")
    J1, J1p, J1pp = get_Jn_derivs(1)
    W1 = sp.simplify(J1 * J1pp - J1p**2)
    # Structure: Y^5 * exp(-2Y) * P_S1(Y) / (scaling factors)
    # We isolate the polynomial part P_S1. 
    # Note: The raw W1 contains Y^(5/2) * Y^(5/2) = Y^5.
    # We factor out Y^(5/2) * exp(-2Y) to match the Lemma definition.
    term_S1 = sp.simplify(W1 / (Y**sp.Rational(5,2) * sp.exp(-2*Y)))
    
    # 3. Derive T_12 and extract P_T12
    print("Deriving T_{12}...")
    J2, J2p, J2pp = get_Jn_derivs(2)
    T12 = sp.simplify(J1 * J2pp + J2 * J1pp - 2 * J1p * J2p)
    term_T12 = sp.simplify(T12 / (Y**sp.Rational(5,2) * sp.exp(-5*Y)))

    print(f"\nPolynomial P_S1(Y): {term_S1}")
    print(f"Polynomial P_T12(Y): {term_T12}")

    # 4. Verify the Dominance Inequality (Lemma 4.3)
    # We define Q(Y) and R(Y) such that:
    # P_S1 = -Y * Q(Y)   (Since P_S1 is negative for Y>pi)
    # P_T12 = 4Y * R(Y)
    
    Q = sp.simplify(-term_S1 / Y)
    R = sp.simplify(term_T12 / (4*Y))
    
    print(f"\nQ(Y): {Q}")
    print(f"R(Y): {R}")
    
    # We verify R(Y)/Q(Y) <= 250 Y  =>  S(Y) = 250*Y*Q - R >= 0
    print("\nConstructing S(Y) = 250*Y*Q(Y) - R(Y)...")
    S = sp.expand(250 * Y * Q - R)
    print(f"S(Y): {S}")
    
    # 5. Rigorous Root Finding for S(Y)
    # We check real roots of S(Y). 
    # If S(Y) has positive leading coeff and no roots on [0, inf), and S(0)>0, then S(Y)>0 globally.
    roots = sp.real_roots(S)
    positive_roots = [r for r in roots if r > 0]
    
    print("\n--- Verification Results ---")
    print(f"Leading coefficient of S(Y): {S.coeff(Y, sp.degree(S, Y))}")
    print(f"Value at Y=0: {S.subs(Y, 0)}")
    print(f"Real roots of S(Y): {roots}")
    
    if S.coeff(Y, sp.degree(S, Y)) > 0 and S.subs(Y, 0) > 0 and len(positive_roots) == 0:
        print("VERIFIED: S(Y) > 0 for all Y >= 0.")
        print("Consequently, |T_12| < 1000 Y e^(-3Y) |W(J_1)| holds.")
    else:
        print("FAILED: Inequality verification failed.")

if __name__ == "__main__":
    verify_polynomials()
```

### Supplementary Material S3: Rigorous Interval Arithmetic Verification

**Purpose:** This script uses the `mpmath` library (arbitrary-precision interval arithmetic) to rigorously certify two key bounds on compact intervals:
1.  $E(Z) > 0$ on $[2\pi-3, 4]$ (Component log-concavity).
2.  $\rho(Y) < 0.08$ on $[\pi, 8]$ (Two-body dominance safety margin).

```python
"""
Supplementary Material S3: Rigorous Interval Arithmetic Verification
References: Theorem 1.2 and Lemma 4.3.
"""
import mpmath as mp
from mpmath import iv

# Set precision to 50 decimal places for rigorous bounds
mp.mp.dps = 50

def verify_intervals():
    print("--- S3: Interval Arithmetic Verification ---")
    
    # --- PART A: Verification of E(Z) > 0 ---
    print("\n[Part A] Verifying E(Z) > 0 on [2pi-3, 4]...")
    
    def E_rational(z):
        # E(Z) = Z^2 + Z - 3/4 - 9/(2Z^2) + 360/Z^3 + 864/Z^4
        return z**2 + z - iv.mpf('0.75') - iv.mpf('4.5')/(z**2) + \
               iv.mpf('360')/(z**3) + iv.mpf('864')/(z**4)

    pi_iv = iv.pi
    z_start = 2 * pi_iv - 3
    z_end = iv.mpf('4')
    
    # Subdivide to prevent interval explosion
    steps = 1000
    step_size = (z_end - z_start) / steps
    min_E = iv.inf
    
    for i in range(steps):
        z_a = z_start + i * step_size
        z_b = z_start + (i + 1) * step_size
        z_interval = iv.mpf([z_a.a, z_b.b])
        val = E_rational(z_interval)
        if val.a < min_E:
            min_E = val.a
            
    print(f"Minimum lower bound of E(Z) on interval: {min_E}")
    if min_E > 25:
        print("VERIFIED: E(Z) > 25.0 for all Z in critical interval.")
    else:
        print("FAILED: E(Z) bound not met.")

    # --- PART B: Verification of rho(Y) < 0.08 ---
    print("\n[Part B] Verifying rho(Y) < 0.08 on [pi, 8]...")
    
    # Polynomials P_S1 and P_T12 (Coefficients from S2)
    # P_S1 = -64Y^5 + 480Y^4 - 1380Y^3 + 1380Y^2 - 675Y
    # P_T12 = 36864Y^6 - 193280Y^5 + 368160Y^4 - 299400Y^3 + 118140Y^2 - 13500Y
    # Note: Coefficients derived in S2. P_T12 is 4Y * R(Y).
    
    def P_S1_interval(y):
        return -64*y**5 + 480*y**4 - 1380*y**3 + 1380*y**2 - 675*y
        
    def P_T12_interval(y):
        return 36864*y**6 - 193280*y**5 + 368160*y**4 - 299400*y**3 + 118140*y**2 - 13500*y
        
    y_start = pi_iv
    y_end = iv.mpf('8')
    steps = 1000
    step_size = (y_end - y_start) / steps
    max_rho = iv.mpf('-inf')
    
    for i in range(steps):
        y_a = y_start + i * step_size
        y_b = y_start + (i + 1) * step_size
        y_int = iv.mpf([y_a.a, y_b.b])
        
        # Calculate |P_S1| (It is negative, so take negative)
        abs_ps1 = -P_S1_interval(y_int)
        pt12 = P_T12_interval(y_int)
        
        # rho(Y) = e^(-3Y) * P_T12 / |P_S1|
        # Note: exp(-3Y) is decreasing. Max is at y_a.
        # Interval arithmetic handles this automatically.
        rho = iv.exp(-3 * y_int) * pt12 / abs_ps1
        
        if rho.b > max_rho:
            max_rho = rho.b

    print(f"Maximum upper bound of rho(Y) on [pi, 8]: {max_rho}")
    if max_rho < 0.08:
        print("VERIFIED: rho(Y) < 0.08 for all Y in [pi, 8].")
    else:
        print("FAILED: rho(Y) bound exceeded.")

if __name__ == "__main__":
    verify_intervals()
```

### Supplementary Material S4: Tail Summation Verification

**Purpose:** This script explicitly calculates the upper bound for the tail contribution $\sum_{(n,m) \ne (1,2)} |T_{nm}| / |W(J_1)|$ at $Y=\pi$. It uses the rigorous "crude" bounds derived in Appendix A ($|T_{nm}| \le C Y^{17/2} \dots$) and sums them for small indices, while bounding the infinite remainder geometrically. This certifies Lemma 4.4.

```python
"""
Supplementary Material S4: Tail Summation and Remainder Bound
References: Lemma 4.4 and Appendix A bounds.
"""
import mpmath as mp
from mpmath import iv

mp.mp.dps = 50

def verify_tail():
    print("--- S4: Tail Dominance Verification ---")
    
    # Constants derived in Appendix A
    # |T_nm(Y)| <= C_T * Y^(17/2) * (nm)^10 * exp(-(n^2+m^2)Y)
    C_T = iv.mpf('125636')
    
    # Lower bound for |W(J_1)| at Y=pi
    # From S2/S3, |P_S1(pi)| is computed rigorously.
    pi_val = iv.pi
    
    # Calculate |P_S1(pi)| rigorously
    def P_S1_eval(y):
        return -(-64*y**5 + 480*y**4 - 1380*y**3 + 1380*y**2 - 675*y) # Abs value
        
    val_PS1_pi = P_S1_eval(pi_val)
    print(f"|P_S1(pi)| lower bound: {val_PS1_pi.a}")
    
    # |W(J_1)(Y)| = Y^(5/2) * exp(-2Y) * |P_S1(Y)|
    # We analyze the ratio R_nm(Y) = |T_nm| / |W(J_1)|
    # R_nm(Y) <= (C_T / |P_S1|) * Y^6 * (nm)^10 * exp(-((n^2+m^2)-2)Y)
    # This ratio is strictly decreasing for Y >= pi. Max is at pi.
    
    def get_term_bound(n, m):
        # Exponent factor: exp(-((n^2+m^2)-2)*pi)
        decay_exp = (n**2 + m**2 - 2) * pi_val
        decay = iv.exp(-decay_exp)
        
        # Polynomial factors at pi
        poly_factor = (pi_val**6) * ((n * m)**10)
        
        # Prefactor ratio
        const_ratio = C_T / val_PS1_pi
        
        return const_ratio * poly_factor * decay

    print("\nSumming explicit bounds for 1 <= n < m <= 6 (excluding 1,2)...")
    total_tail = iv.mpf(0)
    
    # Explicit Summation Loop
    N_limit = 6
    for n in range(1, N_limit + 1):
        for m in range(n + 1, N_limit + 1):
            if n == 1 and m == 2:
                continue # Skip dominant interaction
            
            term = get_term_bound(n, m)
            total_tail += term
            # print(f"Term ({n},{m}): {term.b}")

    print(f"Sum (n,m <= 6): {total_tail.b}")

    print("\nBounding Remainder (max(n,m) > 6)...")
    # Remainder logic: The terms decay super-geometrically. 
    # The term (1, 7) dominates the remainder. 
    # Decay factor is exp(-(50-2)pi) = exp(-48pi) approx 1e-65.
    # The polynomial factor (nm)^10 is approx (7)^10 approx 2e8.
    # The bound is astronomically small. We add a conservative safety epsilon.
    
    # Let's rigorously bound term (1,7) and multiply by a generous factor for the series.
    term_1_7 = get_term_bound(1, 7)
    print(f"Leading remainder term (1,7): {term_1_7.b}")
    
    # Conservative geometric series factor (generous overestimate)
    remainder_bound = term_1_7 * 1000 
    
    total_tail_bound = total_tail + remainder_bound
    
    print(f"\nTotal Tail Bound ratio: {total_tail_bound.b}")
    
    if total_tail_bound.b < 0.03:
        print("VERIFIED: Total tail contribution < 0.03 * |W(J_1)|.")
    else:
        print("FAILED: Tail too large.")

if __name__ == "__main__":
    verify_tail()
```
--

***

### Appendix A: Derivation of Uniform Derivative Bounds

In this appendix, we derive explicit, uniform upper bounds for the components $J_n(u)$ and their derivatives with respect to $u$. These bounds are required to prove the convergence of the tail sum in Lemma 4.4.

Let $Y = \pi e^{2u}$. The domain $u > 0$ corresponds to $Y > \pi$. Since we seek upper bounds, we extend the domain to $Y \ge 1$.
The differential operator with respect to $u$ acts on functions of $Y$ as:
$$ \frac{d}{du} = \frac{dY}{du} \frac{d}{dY} = 2\pi e^{2u} \frac{d}{dY} = 2Y \frac{d}{dY}. $$

#### A.1 Explicit Form of Derivatives
The component $K_n(u)$ is defined in terms of $Y$ as (omitting the factor of 2 for the kernel definition which cancels in the sign analysis, or tracking it consistently):
$$ K_n(Y) \propto Y^{5/4}(2n^4 Y - 3n^2)e^{-n^2Y}. $$
Let $J_n(Y) = -K_n'(u)$. Applying the operator $D = 2Y \frac{d}{dY}$ repeatedly, the exact polynomial structures for $J_n$ and its first two derivatives are:

1.  **Function $J_n(Y)$:**
    $$ J_n(Y) = \frac{n^2}{2} Y^{5/4} e^{-n^2Y} \left( 8n^4 Y^2 - 30n^2 Y + 15 \right). $$

2.  **First Derivative $J_n'(Y)$:**
    $$ J_n'(Y) = \frac{n^2}{4} Y^{5/4} e^{-n^2Y} \left( -32n^6 Y^3 + 224n^4 Y^2 - 330n^2 Y + 75 \right). $$

3.  **Second Derivative $J_n''(Y)$:**
    $$ J_n''(Y) = \frac{n^2}{8} Y^{5/4} e^{-n^2Y} \left( 128n^8 Y^4 - 1440n^6 Y^3 + 4232n^4 Y^2 - 3270n^2 Y + 375 \right). $$

#### A.2 Uniform Bounding Coefficients
We bound these expressions for $Y \ge 1$ and $n \ge 1$.
**Strategy:** We bound the polynomial part by replacing $Y^k$ with $Y^{d}$ (where $d$ is the degree) and summing the absolute values of the coefficients. We use $n^k \le n^{d_n}$.

**1. Bound for $|J_n(Y)|$:**
$$ |8n^4 Y^2 - 30n^2 Y + 15| \le (8+30+15) n^4 Y^2 = 53 n^4 Y^2. $$
Substituting into the expression for $J_n$:
$$ |J_n(Y)| \le \frac{n^2}{2} (53 n^4 Y^2) Y^{5/4} e^{-n^2Y} = 26.5 n^6 Y^{13/4} e^{-n^2Y}. $$
We define the constant $A = 27$ such that:
$$ |J_n(Y)| \le A n^6 Y^{13/4} e^{-n^2Y}. $$

**2. Bound for $|J_n'(Y)|$:**
Sum of absolute coefficients: $32 + 224 + 330 + 75 = 661$.
$$ |J_n'(Y)| \le \frac{n^2}{4} (661 n^6 Y^3) Y^{5/4} e^{-n^2Y} = 165.25 n^8 Y^{17/4} e^{-n^2Y}. $$
We define the constant $B = 166$ such that:
$$ |J_n'(Y)| \le B n^8 Y^{17/4} e^{-n^2Y}. $$

**3. Bound for $|J_n''(Y)|$:**
Sum of absolute coefficients: $128 + 1440 + 4232 + 3270 + 375 = 9445$.
(Note: To be strictly conservative against any potential minor coefficient arithmetic variations in higher order terms, we utilize an upper bound sum of 10445 in the calculations below).
$$ |J_n''(Y)| \le \frac{n^2}{8} (10445 n^8 Y^4) Y^{5/4} e^{-n^2Y} \approx 1305.6 n^{10} Y^{21/4} e^{-n^2Y}. $$
We define the constant $C = 1306$ such that:
$$ |J_n''(Y)| \le C n^{10} Y^{21/4} e^{-n^2Y}. $$

#### A.3 Bounds for Wronskian and Interaction Terms
Using the triangle inequality on $T_{nm} = J_n J_m'' + J_m J_n'' - 2 J_n' J_m'$:

$$ |T_{nm}| \le |J_n||J_m''| + |J_m||J_n''| + 2|J_n'||J_m'|. $$

Substituting the bounds $A, B, C$:
1.  $|J_n||J_m''| \le (A n^6 Y^{13/4}) (C m^{10} Y^{21/4}) e^{-(n^2+m^2)Y} = (A \cdot C) n^6 m^{10} Y^{17/2} e^{-(n^2+m^2)Y}$.
2.  $2|J_n'||J_m'| \le 2 (B n^8 Y^{17/4}) (B m^8 Y^{17/4}) e^{-(n^2+m^2)Y} = (2 B^2) n^8 m^8 Y^{17/2} e^{-(n^2+m^2)Y}$.

We simplify the powers of $n, m$. For $n, m \ge 1$:
$n^6 m^{10} + m^6 n^{10} \le 2 (nm)^{10}$.
$n^8 m^8 \le (nm)^{10}$.

The coefficient for the bound is:
$$ C_{tail} = 2(A \cdot C) + 2(B^2) = 2(27 \cdot 1306) + 2(166^2) = 70524 + 55112 = 125636. $$

**Result:** For all $Y \ge 1$ and $n, m \ge 1$,
$$ |T_{nm}(Y)| \le 125636 \cdot Y^{17/2} (nm)^{10} e^{-(n^2+m^2)Y}. $$

This is the explicit bound utilized in Lemma 4.4 and verified in Supplementary Material S4.
