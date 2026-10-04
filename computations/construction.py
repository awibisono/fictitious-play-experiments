#!/usr/bin/env python3
r"""Exact checks of the uniform RPS-based fictitious-play construction.

The base is the three-action order-two RPS clock, reindexed once so every
reference gain is 1/2. The same lift constructs all later orders, with
n_k=(k+1)^2-5 after one final setup action. Finite computations supplement,
but do not replace, an all-order proof.
"""

from __future__ import annotations

if not __debug__:
    raise RuntimeError("Run exact verification without Python -O or -OO.")

import argparse
from dataclasses import dataclass
from functools import lru_cache
from math import comb, factorial, lcm
import sys

sys.dont_write_bytecode = True
import time
from typing import Callable
import sympy as s

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

R = s.Rational


def ck(value, message: str):
    if not value:
        raise AssertionError(message)


def rownorm(a):
    return sum(abs(x) for x in a)


def star(a):
    if not a.rows or not a.cols:
        return R(0)
    return max(
        max(sum(abs(a[i, j]) for j in range(a.cols)) for i in range(a.rows)),
        max(sum(abs(a[i, j]) for i in range(a.rows)) for j in range(a.cols)),
    )


def rho(w: int):
    return s.Matrix([[1] + [0] * (w - 1)])


@lru_cache(None)
def conversion(w: int):
    """p_Newton(q) = conversion(w) * p_divided_power(q)."""
    q = s.Symbol("q")
    return s.Matrix(
        w,
        w,
        lambda j, k: s.Poly(
            s.prod(q - i for i in range(j)) / s.factorial(j), q
        ).coeff_monomial(q**k)
        * s.factorial(k),
    )


@lru_cache(None)
def shift(w: int):
    T = s.eye(w)
    for j in range(1, w):
        T[j, j - 1] = 1
    return T


@lru_cache(None)
def divided_shift(w: int, t=1):
    return s.Matrix(
        w, w, lambda i, j: R(t) ** (i - j) / s.factorial(i - j) if i >= j else 0
    )


@lru_cache(None)
def evaluate(w: int, factor: int = 1, offset: int = 0, out=None, basis: str = "newton"):
    out = out or w
    D = s.Matrix(
        w,
        out,
        lambda i, j: (
            s.binomial(i, j)
            * factor**j
            * offset ** (i - j)
            * s.factorial(j)
            / s.factorial(i)
            if j <= i
            else 0
        ),
    )
    if basis == "divided":
        return D
    return s.simplify(conversion(w) * D * conversion(out).inv())


@lru_cache(None)
def sum_map(parent_w: int, stride: int = 1, basis: str = "newton"):
    """f(row) * sum_map represents sum_{r=stride*q}^{2*stride*q-1} f(r)."""
    w = parent_w + 1
    values = s.Matrix(
        w,
        parent_w,
        lambda k, j: (
            s.prod(2 * stride * k - i for i in range(j + 1))
            - s.prod(stride * k - i for i in range(j + 1))
        )
        / s.factorial(j + 1),
    )
    vand = s.Matrix(w, w, lambda k, j: s.binomial(k, j))
    F = (vand.inv() * values).T
    if basis == "newton":
        return F
    return s.simplify(conversion(parent_w).inv() * F * conversion(w))


@lru_cache(None)
def cokernel(d: int, basis: str = "newton"):
    w = d + 1
    bh = divided_shift(w, R(-1, 2))
    ans = []
    for h in range(d, 2 * d + 1):
        if h % 2:
            continue
        V = s.Matrix(w, w, lambda i, j: (-1) ** i if i + j == h else 0)
        Z = bh * V
        ck(Z == divided_shift(w, -1) * Z.T, "divided-power cokernel equation")
        if basis == "newton":
            Z = conversion(w) * Z * conversion(w).T
        ans.append((h, Z))
    return tuple(ans)


def inner(A, B):
    return sum(x * y for x, y in zip(A, B))


@lru_cache(None)
def operator(w: int):
    B = shift(w).inv()
    L = s.Matrix(
        w * w,
        w * w,
        lambda l, k: int(l == k) - (B[k // w, l % w] if l // w == k % w else 0),
    )
    rr = L.T.rref()[1]
    cc = L.rref()[1]
    core = L.extract(rr, cc).inv()
    P = s.zeros(w * w, w * w)
    for i, ci in enumerate(cc):
        for j, rj in enumerate(rr):
            P[ci, rj] = core[i, j]
    ck(L * P * L == L, "linear right inverse on the range")
    return L, P


def inverse_moment(F):
    w = F.rows
    return s.Matrix(w, w, list(operator(w)[1] * s.Matrix(list(F))))


def summary(H, ctot, rb, terminal, d: int, stride, c=R(1, 2), basis: str = "newton"):
    w = d + 1
    F = sum_map(d, stride, basis)
    E = evaluate(d, stride, 0, w, basis)
    E2 = evaluate(d, 2 * stride, 0, w, basis)
    T = shift(w) if basis == "newton" else divided_shift(w)
    rh = rho(w)
    L = E * (T - s.eye(w)) - (E2 - E)
    f = rb * E2 - rb * E * T + c * rh
    A = L.T * H * F + f.T * (ctot * F) + rh.T * (rb * (E2 - E) + terminal * F)
    A += (rb * L + f - terminal * F * T).T * rh
    return s.expand(A), s.expand(ctot * F + rh), s.expand(-(rb * (E2 - E) + c * rh))


def integer_stride(H, ctot, rb, terminal, d: int):
    z = s.Symbol("stride", positive=True)
    C = conversion(d)
    A, _, dy = summary(
        C.T * H * C, ctot * C, rb * C, terminal * C, d, z, basis="divided"
    )
    ell = s.zeros(1, d + 1)
    eqs = [
        (h, Z)
        for h, Z in cokernel(d, "divided")
        if h < 2 * d and not (d % 2 == 0 and h == d)
    ]
    for h, Z in reversed(eqs):
        i = h - d + 1
        coef = s.expand(sum(Z[i, j] * dy[j] for j in range(d + 1)))
        val = s.cancel(s.expand(inner(Z, A - ell.T * dy)) / coef)
        ell[i] = val
    den = 1
    for value in ell:
        for a in s.Poly(value, z).all_coeffs():
            den = lcm(den, int(a.q))
    stride = den * factorial(d)
    ev = ell.subs(z, stride)
    newton = ev * conversion(d + 1).inv()
    ck(all(a.q == 1 for a in newton), "integer Newton coefficients")
    return int(stride), newton


def future_target(rb, d: int, stride: int, c0=R(1, 2)):
    w = d + 2
    B = shift(w).inv()
    rh = rho(w)
    E = evaluate(d + 1, stride, 0, w)
    E2 = evaluate(d + 1, 2 * stride, 0, w)
    back = rb * (E2 - E) + c0 * rh
    forward = back * shift(w)
    y = s.Matrix([[0, *list(forward)[:-1]]])
    g = y + y * B + c0 * rh
    F = sum_map(d + 1, stride)
    target = g[:, 1:] * F[:, 1:].inv()
    ck(target * F == g, "future cone target identity")
    return target


def left_inverse_transpose(X):
    L = X * (X.T * X).inv()
    ck(X.T * L == s.eye(X.cols), "Gram right inverse of X.T")
    return L


def power_coeffs(row: s.Matrix):
    divided = row * conversion(row.cols)
    return [divided[j] / s.factorial(j) for j in range(row.cols)]


def positive(row: s.Matrix, key: str):
    coeff = power_coeffs(row)
    while coeff and coeff[-1] == 0:
        coeff.pop()
    ck(bool(coeff) and coeff[-1] > 0, "eventual strict positivity: " + key)
    degree = len(coeff) - 1
    threshold = (
        1
        if degree == 0
        else int(s.floor(sum(abs(a) for a in coeff[:-1]) / coeff[-1])) + 2
    )
    return dict(key=key, degree=degree, threshold=str(threshold))


@dataclass
class Parent:
    order: int
    G: s.Matrix
    R: s.Matrix
    C: s.Matrix
    b: int
    tau: int | s.Matrix
    delta0: s.Rational
    threshold: int
    allowance: int
    charges: list
    suffix_threshold_fn: Callable[[s.Rational], int]
    stride: int
    particular: s.Matrix
    cone: s.Matrix
    name: str


def bernstein(expr, variable):
    p = s.Poly(s.expand(expr), variable)
    degree = p.degree()
    if p.is_zero:
        return [s.S.Zero]
    return [
        s.expand(sum(p.nth(l) * R(comb(i, l), comb(degree, l)) for l in range(i + 1)))
        for i in range(degree + 1)
    ]


def nonnegative_coeffs(expr, syms):
    poly = s.Poly(s.expand(expr), *syms)
    return all(c >= 0 for c in poly.coeffs()) if poly.coeffs() else True


def verify_cokernel_linear_algebra(max_d: int = 9):
    """Independently verifies the cokernel basis and rank of L(E) = E - E^T B for d = 2..max_d."""
    for d in range(2, max_d + 1):
        w = d + 1
        L_mat, _ = operator(w)
        expected_corank = (d + 2) // 2
        actual_corank = w * w - L_mat.rank()
        ck(
            actual_corank == expected_corank,
            f"corank of L at d={d} is {expected_corank}",
        )
        basis_newton = cokernel(d, "newton")
        ck(len(basis_newton) == expected_corank, f"cokernel basis count at d={d}")
        rows = []
        for h, Z in basis_newton:
            vec = s.Matrix(1, w * w, list(Z))
            ck(
                vec * L_mat == s.zeros(1, w * w),
                f"Z^({h}) in left kernel of L at d={d}",
            )
            rows.append(vec)
        stacked = s.Matrix.vstack(*rows)
        ck(stacked.rank() == expected_corank, f"Z^({h}) basis has full rank at d={d}")


def build_and_verify_rps_core() -> Parent:
    q, x = s.symbols("q x")
    G = s.Matrix([[0, -1, 1], [1, 0, -1], [-1, 1, 0]])
    Rt = s.Matrix([[1, 1], [-R(11, 3), -2], [R(2, 3), 1]])
    C = s.Matrix([[5, 3], [6, 3], [7, 3]])
    v = s.Matrix([[0, -1, 1]])
    pq = s.Matrix([1, q])
    state = Rt * pq
    ck(G * C == Rt * (shift(2) - s.eye(2)), "RPS polynomial reset")
    ck(C[:2, :].det() == -3 and C.rank() == 2, "RPS full count rank")
    checks = 0
    remaining = C * pq
    for i in range(3):
        length = (C * pq)[i]
        ck(positive(C[i, :], f"RPS.length.{i}")["degree"] == 1, "positive RPS run")
        for offset in [0, length - 1]:
            at = state + offset * G[:, i]
            for j in range(3):
                if j != i:
                    diff = s.expand((at[i] - at[j]).subs(q, x + 1))
                    ck(
                        nonnegative_coeffs(diff, (x,)) and diff.subs(x, 0) > 0,
                        "RPS strict proper-prefix margin",
                    )
                    checks += 1
        h = s.symbols("h")
        rem_expr = s.expand((v * (remaining - h * s.eye(3)[:, i]))[0])
        expected = [1, 1 + h, 3 * q + 7 - h][i]
        ck(s.expand(rem_expr - expected) == 0, "RPS proper-prefix remaining counter")
        remaining -= length * s.eye(3)[:, i]
        state += length * G[:, i]
    ck(state == Rt * s.Matrix([1, q + 1]), "RPS complete phase return")
    safe = Rt * pq + G[:, 0] - v.T
    ck(
        s.expand(safe[0] - safe[1]) == 3 * q + R(8, 3) and safe[0] - safe[2] == R(7, 3),
        "RPS signed-counter entry safety",
    )
    ck(v * C == rho(2), "RPS unit counter")
    cone = s.Matrix([R(2, 27)] * 3)
    ell = s.zeros(1, 3)
    ck(
        cone.T * C == future_target(Rt[0, :], 1, 1),
        "RPS positive weights with reference 1/2",
    )
    ans = Parent(
        order=2,
        G=G,
        R=Rt,
        C=C,
        b=0,
        tau=v,
        delta0=R(1),
        threshold=1,
        allowance=1,
        charges=[("base.complete_RPS", s.ones(1, 3) * C, rho(2))],
        suffix_threshold_fn=lambda eps: 1,
        stride=1,
        particular=ell,
        cone=cone,
        name="rps_order_2",
    )
    o = interface_general(ans, 1, R(1, 2), R(1, 4), 4)
    ck(
        o["X"] == s.Matrix([[0, 8, 9], [0, 9, 9], [0, 10, 9], [1, 0, 0]]),
        "RPS old-count table",
    )
    ck(o["y"] == s.Matrix([[4, R(3, 2), 1]]), "RPS reference-height row")
    moment = o["D"].T * o["X"]
    ck(
        moment == s.Matrix([[-R(1, 2), -R(23, 2), -R(27, 2)], [-1, 27, 27], [0, 0, 0]]),
        "RPS reference moment table",
    )
    ck(inner(dict(cokernel(2))[2], moment) == -R(81, 2), "RPS lowest even-degree test")
    ck(inner(dict(cokernel(2))[4], moment) == 0, "RPS higher test vanishes")
    print(
        f"CHECKED RPS base: {checks} strict symbolic endpoint margins, signed counter, reset, positive weights and both moment tests."
    )
    return ans


def interface_general(p: Parent, stride: int, c, delta, H):
    """Computes old-block gateway tables with consistent flat height normalization y(0) = H."""
    d = p.order
    w = d + 1
    m = p.G.rows
    rh = rho(w)
    T = shift(w)
    B = T.inv()
    N = T - s.eye(w)
    F = sum_map(d, stride)
    E = evaluate(d, stride, 0, w)
    E2 = evaluate(d, 2 * stride, 0, w)
    Xp = p.C * F
    RE = p.R * E
    R2 = p.R * E2
    v = s.zeros(1, m) if isinstance(p.tau, int) else p.tau
    if isinstance(p.tau, int):
        v[p.tau] = 1
    ck(p.G * Xp == R2 - RE, "parent bundled reset")
    ck(v * Xp == s.Matrix([[0, stride] + [0] * (d - 1)]), "terminal counter count")
    back = p.R[p.b, :] * (E2 - E) + c * rh
    forward = back * T
    y = s.Matrix([[H, *list(forward)[:d]]])
    ck(y * (s.eye(w) - B) == back and y[0] == H, "y difference equation and y(0) = H")
    h = y * B - p.R[p.b, :] * E
    SP = RE + s.ones(m, 1) * h
    S = SP.col_join(y * B - v * Xp + delta * rh)
    grow = p.G[p.b, :] + v
    G = p.G.row_join(-grow.T).col_join(grow.row_join(s.zeros(1)))
    X = Xp.col_join(rh)
    O = S + G * X
    D = S * N - G * X
    ck(S[p.b, :] == y * B, "S_{b,:} = yB")
    ck(O[p.b, :] == y - c * rh, "O_{b,:} = y - c rho")
    ck(O[m, :] == y - (c - delta) * rh, "O_{g,:} = y - (c - delta) rho")
    ck(D[:, d] == s.zeros(m + 1, 1), "top-null reset demand")
    ck(S[:, d] == y[d] * s.ones(m + 1, 1), "common old leading score column")
    return dict(
        G=G,
        S=S,
        O=O,
        X=X,
        D=D,
        y=y,
        h=h,
        Xp=Xp,
        RE=RE,
        R2=R2,
        F=F,
        T=T,
        B=B,
        N=N,
        rho=rh,
        delta=delta,
        c=c,
        H=H,
        v=v,
    )


def closed_form_W_inverse(u: s.Matrix, radius: int, d: int) -> s.Matrix:
    """Exact closed-form inverse W^{-1} = T_*^{-1} Phi_0 + A_circ^{-1} Phi_1."""
    r = d + 1
    e_d = s.zeros(r, 1)
    e_d[d, 0] = 1
    Pi = s.eye(d).row_join(s.zeros(d, 1)) - s.ones(d, r) / r
    term0 = (e_d * s.ones(1, r)) / (r * u[d])
    term1 = (s.eye(d).col_join(-u[:, :d] / u[d]) * Pi) / radius
    return term0 + term1


def sherman_morrison_WE_inverse(W_inv: s.Matrix, ell1: s.Matrix, r: int) -> s.Matrix:
    """Exact Sherman-Morrison inverse (W + e_0 ell_*)^{-1}."""
    e_0 = s.zeros(r, 1)
    e_0[0, 0] = 1
    denom = 1 + (ell1 * W_inv * e_0)[0, 0]
    ck(denom != 0, "Sherman-Morrison denominator nonzero")
    return W_inv - (W_inv * e_0 * ell1 * W_inv) / denom


def select_scale_closed_form(
    o, a, ell1, d: int, allowance: int, c0, verbose: bool = False
):
    """Executes the doubling scale search T_* = 1, 2, 4, ... using the explicit scale bounds in the construction."""
    w = d + 1
    r = w
    m = o["X"].rows
    rh = rho(w)
    B = o["B"]
    X = o["X"]
    D0 = o["D"]
    y0 = o["y"]
    lam = 1
    for value in y0:
        lam = lcm(lam, int(value.q))
    ell0 = 2 * r * lam * y0
    E0 = 2 * r * lam * y0.T * y0
    dy0 = y0 * B - y0
    A0 = D0.T * X
    xt = s.ones(1, m) * X
    residual = R(0)
    if d % 2 == 0:
        zmin = dict(cokernel(d))[d]
        residual = inner(zmin, A0 - ell1.T * dy0)
    E1 = inverse_moment(A0 - ell1.T * dy0)
    E2 = inverse_moment(rh.T * xt + ell1.T * rh)
    E3 = inverse_moment(ell0.T * rh)
    LX = left_inverse_transpose(X)
    simplex = s.zeros(r, w)
    for i in range(d):
        simplex[i, i] = 1
        simplex[d, i] = -1
    e_d = s.zeros(r, 1)
    e_d[d, 0] = 1
    Phi0 = (e_d * s.ones(1, r)) / (r * lam * y0[d])
    Pi = s.eye(d).row_join(s.zeros(d, 1)) - s.ones(d, r) / r
    Phi1 = s.eye(d).col_join(-y0[:, :d] / y0[d]) * Pi
    Lr = s.Matrix(r, r, lambda i, j: 1 if i > j else 0)
    amin = min(a)
    ag = a[-1]
    Tscale = 1
    while True:
        ell = Tscale * ell0 + ell1
        den = xt[d] + ell[d]
        if d % 2 == 0 and den <= 0:
            Tscale *= 2
            continue
        c = c0 if d % 2 else (c0 - residual / den)
        dc = c - c0
        u = Tscale * lam * y0
        g = u[d]
        gfirst = g + ell1[d]
        A_min = int(u[d])
        if not (0 < c < 1 and gfirst > 0 and A_min >= Tscale):
            Tscale *= 2
            continue
        bW = (star(Phi0) + star(Phi1)) / Tscale
        nu = bW * rownorm(ell1)
        if nu >= R(1, 2):
            Tscale *= 2
            continue
        y = y0 + dc * s.Matrix([[0, 1] + [0] * (d - 1)])
        D = D0 + dc * s.ones(m, 1) * rh
        E = Tscale * E0 + E1 + dc * E2 + Tscale * dc * E3
        bE = bW / (1 - nu)
        k0 = R(2, r * lam * Tscale)
        bC = star(s.ones(r, 1) * lam * y0) + star(simplex) + rownorm(ell1) / Tscale
        Ebase = Tscale * E0 + 2 * y0.T * ell1
        bR = star(E - Ebase) + 2 * star(Lr) * bC**2 / Tscale
        bCross = bW * bR * bE
        dy = y * B - y
        bQ = 2 * r * rownorm(dy - dy0) + k0 * r * rownorm(ell1)
        bQ += 4 * star(Lr) * bC * (1 + star(B)) / (Tscale**2)
        bQ += bR * (bE * star(B) + bW)
        RD = D + a * ell1
        bP = star(RD) * bW + star(LX) * (bQ + star(X) * star(RD) * bW)
        if bCross < k0 / 2 and bP < min(amin / 4, (ag - allowance - 1) / 2):
            break
        Tscale *= 2
    if verbose:
        print(
            f"  scale selected: T_* bits={Tscale.bit_length()}, A_min bits={A_min.bit_length()}",
            flush=True,
        )
    return dict(
        Tscale=Tscale,
        A_min=A_min,
        lam=lam,
        c=c,
        y=y,
        D=D,
        E=E,
        ell=ell,
        E0=E0,
        y0=y0,
        u=u,
        LX=LX,
        simplex=simplex,
        Phi1=Phi1,
        Lr=Lr,
        k0=k0,
    )


def verify_lift(wit):
    """Verifies all algebraic resets, support-safety, early/late signs & reserves, and thresholds."""
    p = wit["parent"]
    o = wit["interface"]
    out = wit["output_parent"]
    d = p.order
    w = d + 1
    r = w
    G = wit["G"]
    U = wit["U"]
    P = wit["P"]
    M = wit["M"]
    J = wit["J"]
    y = wit["y"]
    X = o["X"]
    O = o["O"]
    B = o["B"]
    N = o["N"]
    rh = o["rho"]
    v = o["v"]
    m = X.rows
    m_parent = m - 1
    nc = M.rows
    stride = p.stride

    ck(G + G.T == s.zeros(G.rows), "skew matrix")
    ck(P * M == o["D"], "forward reset PM = D")
    dy = y * B - y
    Q = s.ones(nc, 1) * dy + J * M - J.T * M * B
    ck(P.T * X == Q, "reciprocal reset P^T X = Q")
    ck(o["D"].T * X == M.T * Q, "work conservation D^T X = M^T Q")
    ck(M.T * J * M == wit["E"], "exact moment realization M^T J M = E")
    ell_tot = s.ones(1, nc) * M
    F_mat = o["D"].T * X - ell_tot.T * dy
    ck(F_mat[d, d] == 0, "bottom-right entry F_{dd} = 0")
    ck(G * wit["Cphase"] == U * N, "full phase reset")
    ck(G * out.C == out.R * N, "rotated reset")
    ck(out.C[out.tau, :] == rh, "one terminal gateway per rotated phase")
    ck(out.C[out.b, :] == M[0, :], "unique first run count")
    ck(out.R[out.b, :] == y, "flat entry height (R_+)_{c_0,:} = y")
    ck(
        0 < o["delta"] < min(o["c"], p.delta0),
        "strict gateway endpoint lead 0 < delta < min(c, delta_0)",
    )
    ck(
        all(J[i, j] > 0 for i in range(nc) for j in range(i)),
        "ordered positive controller J",
    )
    ck(
        max(P[:, :r]) < 0 and min(P[:, r:]) > 0,
        "early/late cross block signs P_E < 0, P_L > 0",
    )

    eps = wit["rho_suffix"]
    # Stronger reserve (Eq. (39)) for EVERY early controller 0 <= j < r:
    ck(
        all(-P[i, j] > eps for i in range(m_parent) for j in range(r)),
        "every early controller remaining-count reserve (-P_{i,j} > eps for all i < m, j < r)",
    )
    ck(
        all(-P[m - 1, j] - o["c"] > p.allowance for j in range(r)),
        "every early controller endpoint reserve (-P_{g,j} - c > A_d for all j < r)",
    )

    # Shorter sign-based chronology threshold Q_out (Section 8.1):
    len_two_certs = [
        positive(M[j, :] - 2 * rh, f"length_at_least_two.{j}") for j in range(nc)
    ]
    Q_len = max(int(c_item["threshold"]) for c_item in len_two_certs)
    suffix_certs = [
        positive(eps * length - gain, "suffix." + name)
        for name, length, gain in p.charges
    ]
    Q_bun = max(
        [p.threshold, p.suffix_threshold_fn(eps)]
        + [int(c_item["threshold"]) for c_item in suffix_certs]
    )
    Q_out = max(1, Q_len + 1, int(s.ceiling(R(Q_bun) / stride)), Q_bun)

    # Verify M(Q_out) >= 2 and M(Q_out - 1) > 0 explicitly at q = Q_out:
    p_q = s.Matrix([s.binomial(Q_out, j) for j in range(w)])
    p_qm1 = s.Matrix([s.binomial(Q_out - 1, j) for j in range(w)])
    ck(min(M * p_q) >= 2 and min(M * p_qm1) >= 1, "M(Q_out) >= 2 and M(Q_out - 1) > 0")

    # Also retain the legacy leading-profile and prefix-debt checks as optional regressions:
    gamma = M[:, d]
    for i in range(m):
        debt = 0
        for j in range(nc):
            debt += P[i, j] * gamma[j]
            ck(debt < 0 if j < nc - 1 else debt == 0, "leading prefix debt")

    certs = list(len_two_certs) + list(suffix_certs)
    certs.append(positive(p.C[p.b, :] - rho(p.C.cols), "parent.first_run_at_least_two"))
    certs.append(positive(out.R[out.b, :], "entry.height"))

    # Support-safety at parent entry: (R(q) + A e_b - v^T)_b > (R(q) + A e_b - v^T)_i for i in supp(v)
    rho_d = rho(d)
    for i in range(m_parent):
        if v[i] != 0:
            diff_row = (p.R[p.b, :] - p.R[i, :]) + (
                p.G[p.b, p.b] - p.G[i, p.b] - v[p.b] + v[i]
            ) * rho_d
            certs.append(positive(diff_row, f"support_safe_parent.{i}"))
    # Support-safety at rotated entry for g = out.tau:
    g_idx = out.tau
    b_new = out.b
    diff_rot = (out.R[b_new, :] - out.R[g_idx, :]) + (
        G[b_new, b_new] - G[g_idx, b_new] + 1
    ) * rh
    certs.append(positive(diff_rot, "support_safe_rotated.g"))

    ck(O[:, d] == y[d] * s.ones(m, 1), "common old leading height")
    partial = s.zeros(m, w)
    for j in range(nc):
        for i in range(m):
            F_ij = y - O[i, :] - partial[i, :] - max(P[i, j], 0) * (M[j, :] - rh)
            certs.append(positive(F_ij, f"old_controller.{i}.{j}"))
        partial += P[:, j] * M[j, :]

    q, theta = s.symbols("q theta")
    rb = p.R[p.b, :]
    uniform = []
    for j in range(1, nc - 1):
        completed = P[:-1, j].T * p.C
        negative = s.zeros(1, d)
        for i in range(m - 1):
            negative += min(P[i, j], 0) * p.C[i, :]
        anti = s.Matrix([[0, *list(completed)]])
        rrow = (rb + negative).row_join(s.zeros(1, 1)) + anti
        qrow = o["h"] - wit["V"][j, :] - anti * evaluate(w, stride, 0, w)
        rp = power_coeffs(rrow)
        qp = power_coeffs(qrow)
        terms = {}
        for degree in range(w):
            for power in range(degree + 1):
                value = rp[degree] * stride**degree * s.binomial(degree, power)
                if power == 0:
                    value += qp[degree]
                if value:
                    terms[(degree, power)] = value
        expr = s.Poly.from_dict(terms, (q, theta))
        lead = s.expand(
            sum(co * theta ** mon[1] for mon, co in expr.terms() if mon[0] == d)
        )
        omega = ((1 + theta) ** d - 1) / (2**d - 1)
        left = (J.T * gamma)[j]
        right = (J * gamma)[j]
        claimed = ((1 - omega) * left + omega * right) / s.factorial(d)
        ck(s.Poly(lead - claimed, theta).is_zero, "uniform leading profile exact")
        mu = min(left, right) / s.factorial(d)
        ck(mu > 0, "uniform strictly positive profile")
        lower = sum(abs(co) for mon, co in expr.terms() if mon[0] < d)
        threshold = int(s.floor(lower / mu)) + 2
        uniform.append(dict(key=f"parent_controller.{j}", threshold=str(threshold)))

    legacy_threshold = max(
        [p.threshold, 1, Q_bun] + [int(x["threshold"]) for x in certs + uniform]
    )
    out.threshold = Q_out
    return dict(
        univariate_count=len(certs),
        uniform_count=len(uniform),
        phase_threshold=Q_out,
        legacy_threshold=legacy_threshold,
    )


def lift_order(p: Parent, verbose: bool = True, plan_next: bool = True):
    """Executes the flat-controller one-step lift from order d to order d+1."""
    d = p.order
    w = d + 1
    r = w
    c0 = R(1, 2)
    H = R(p.allowance + 3)
    m = p.G.rows + 1
    if verbose:
        print(
            f"LIFTING ORDER {d} ({p.G.rows} actions) -> ORDER {d+1} ({p.G.rows + 2*d + 3} actions)",
            flush=True,
        )
    o = interface_general(p, p.stride, c0, min(p.delta0, c0) / 2, H)
    X = o["X"]
    B = o["B"]
    rh = o["rho"]
    Tshift = o["T"]
    a = p.cone.col_join(s.Matrix([2 * H - c0]))
    ell1 = p.particular
    ck(
        a.rows == m and min(a) > 0 and a.T * X == o["y"] + o["y"] * B,
        "input positive cone",
    )
    z = select_scale_closed_form(o, a, ell1, d, p.allowance, c0, verbose)
    scale = z["Tscale"]
    A_min = z["A_min"]
    u = z["u"]
    y = z["y"]
    D = z["D"]
    E = z["E"]
    ell = z["ell"]
    c = z["c"]
    delta = min(p.delta0, c) / 2
    oa = interface_general(p, p.stride, c, delta, H)
    O = oa["O"]
    ck(oa["D"] == D and oa["y"] == y, "D and y independent of delta")
    Hnext = s.Matrix(O.T * X * Tshift + y.T * ell - E.T)
    Hnext[0, :] = s.zeros(1, w)
    cnext = s.ones(1, m) * X * Tshift + ell
    if plan_next:
        snext, l1next = integer_stride(Hnext, cnext, y, rh, d + 1)
        target = future_target(y, d, snext)
    else:
        snext = 1
        l1next = s.zeros(1, w + 1)
        target = y
    rest = s.ones(1, m) * X * Tshift + r * u + ell1
    mu = target[d] / (4 * rest[d])
    remaining = target - mu * rest
    alpha = remaining[d] / (r * u[d])
    simplex = z["simplex"]
    br = remaining * z["Phi1"]
    radius = int(s.floor(max(scale, A_min, 1, 2 * max(abs(t) for t in br) / alpha))) + 1
    W = s.Matrix(s.ones(r, 1) * u + radius * simplex)
    WE = W.copy()
    WE[0, :] += ell1
    M = WE.col_join(W)
    W_inv = closed_form_W_inverse(u, radius, d)
    WE_inv = sherman_morrison_WE_inverse(W_inv, ell1, r)
    ck(
        W * W_inv == s.eye(r) and WE * WE_inv == s.eye(r),
        "exact closed-form inverses W^{-1} and W_E^{-1}",
    )
    weights = remaining * W_inv
    ck(
        weights == alpha * s.ones(1, r) + br / radius,
        "closed-form cone weight identity",
    )
    nextcone = s.Matrix([mu] * (m + r) + list(weights))
    Crot = (X * Tshift).col_join(M)
    ck(
        min(nextcone) > 0 and nextcone.T * Crot == target,
        "future positive cone on every action",
    )
    if verbose:
        print(
            f"  simplex radius bits={radius.bit_length()}, next stride bits={int(snext).bit_length()}",
            flush=True,
        )
    eta = R(1, scale * radius**2)
    Lr = z["Lr"]
    k0 = z["k0"]
    Ebase = scale * z["E0"] + 2 * z["y0"].T * ell1
    Wint = WE.T * Lr * WE + W.T * Lr * W
    cross = k0 * s.ones(r, r) + W_inv.T * (E - Ebase - eta * Wint) * WE_inv
    J = (eta * Lr).row_join(s.zeros(r)).col_join(cross.row_join(eta * Lr))
    K = J - J.T
    P0 = (-a * s.ones(1, r)).row_join(a * s.ones(1, r))
    Q = s.ones(2 * r, 1) * (y * B - y) + J * M - J.T * M * B
    RM = s.zeros(w, r).row_join(W_inv)
    RD = D - P0 * M
    SQ = Q - P0.T * X
    P = P0 + RD * RM + z["LX"] * (SQ.T - X.T * RD * RM)
    rho_suffix = min(a) / 4
    Vscore = s.ones(2 * r, 1) * y * B - J.T * M * B
    G = oa["G"].row_join(P).col_join((-P.T).row_join(K))
    U = oa["S"].col_join(Vscore)
    Cphase = X.col_join(M)
    Rrot = O.col_join(s.ones(2 * r, 1) * y - J * M)
    ck(
        Rrot == U + G * X.col_join(s.zeros(2 * r, w)),
        "R_+ = col(O, 1 y - JM) = U + G col(X, 0)",
    )

    bnew = m
    taunew = m - 1
    charges = p.charges + [
        (f"order{d+1}.complete_A", s.ones(1, m) * X, y - oa["S"][p.b, :]),
        (
            f"order{d+1}.complete_rotated",
            s.ones(1, Crot.rows) * Crot,
            Rrot[bnew, :] * (Tshift - s.eye(w)),
        ),
    ]

    def next_suffix_threshold(eps_val: s.Rational) -> int:
        q_parent = p.suffix_threshold_fn(eps_val)
        q_bundle = int(s.ceiling(R(q_parent) / p.stride))
        q_A = int(
            positive(
                eps_val * s.ones(1, m) * (X * Tshift) - y * (Tshift - s.eye(w)),
                f"rot_B.d{d+1}",
            )["threshold"]
        )
        return max(q_bundle, q_A)

    out = Parent(
        order=d + 1,
        G=G,
        R=Rrot,
        C=Crot,
        b=bnew,
        tau=taunew,
        delta0=R(1),
        threshold=p.threshold,
        allowance=p.allowance + 1,
        charges=charges,
        suffix_threshold_fn=next_suffix_threshold,
        stride=snext,
        particular=l1next,
        cone=nextcone,
        name=f"order{d+1}",
    )
    return dict(
        parent=p,
        output_parent=out,
        interface=oa,
        M=M,
        J=J,
        K=K,
        P=P,
        E=E,
        V=Vscore,
        G=G,
        U=U,
        Cphase=Cphase,
        y=y,
        delta=delta,
        rho_suffix=rho_suffix,
        scale_bits=scale.bit_length(),
        radius_bits=radius.bit_length(),
    )


def verify_radius_cancellations(parent: Parent):
    """Check the expanded radius-uniform identities at three exact radii per parent.

    These finite regressions do not establish uniformity over unbounded radii;
    that conclusion uses the symbolic norm estimates in the construction.
    """
    d = parent.order
    r = d + 1
    cref = R(1, 2)
    H = R(parent.allowance + 3)
    o = interface_general(parent, parent.stride, cref, min(parent.delta0, cref) / 2, H)
    X, B = o["X"], o["B"]
    a = parent.cone.col_join(s.Matrix([2 * H - cref]))
    ellstar = parent.particular
    z = select_scale_closed_form(o, a, ellstar, d, parent.allowance, cref)
    scale, u, y0, y, E, D = (z[k] for k in ["Tscale", "u", "y0", "y", "E", "D"])
    L, kappa, LX = z["Lr"], z["k0"], z["LX"]
    ed = s.zeros(r, 1)
    ed[d] = 1
    phi0 = ed * s.ones(1, r) / (r * z["lam"] * y0[d])
    bw = (star(phi0) + star(z["Phi1"])) / scale
    nu = bw * rownorm(ellstar)
    be = bw / (1 - nu)
    bc = (
        star(s.ones(r, 1) * z["lam"] * y0)
        + star(z["simplex"])
        + rownorm(ellstar) / scale
    )
    ebase = scale * z["E0"] + 2 * y0.T * ellstar
    br = star(E - ebase) + 2 * star(L) * bc**2 / scale
    dy, dy0 = y * B - y, y0 * B - y0
    bq = 2 * r * rownorm(dy - dy0) + kappa * r * rownorm(ellstar)
    bq += 4 * star(L) * bc * (1 + star(B)) / scale**2 + br * (be * star(B) + bw)
    p0 = (-a * s.ones(1, r)).row_join(a * s.ones(1, r))
    dr = D + a * ellstar
    bp = star(dr) * bw + star(LX) * (bq + star(X) * star(dr) * bw)
    amin = int(max(scale, u[d]))
    for radius in [amin, 2 * amin, 17 * amin]:
        W = s.ones(r, 1) * u + radius * z["simplex"]
        WE = W.copy()
        WE[0, :] += ellstar
        wi = closed_form_W_inverse(u, radius, d)
        wei = sherman_morrison_WE_inverse(wi, ellstar, r)
        ck(W * wi == s.eye(r) and WE * wei == s.eye(r), "radius check: exact inverses")
        ck(star(wi) <= bw and star(wei) <= be, "radius check: inverse bounds")
        ck(
            star(W / radius) <= bc and star(WE / radius) <= bc,
            "radius check: normalized counts",
        )
        eta = R(1, scale * radius**2)
        fres = E - ebase - eta * (WE.T * L * WE + W.T * L * W)
        cross = kappa * s.ones(r, r) + wi.T * fres * wei
        ck(
            star(fres) <= br and star(cross - kappa * s.ones(r, r)) <= bw * br * be,
            "radius check: residual and cross-error bounds",
        )
        ck(
            cross * WE
            == 2 * s.ones(r, 1) * y0 + kappa * s.ones(r, 1) * ellstar + wi.T * fres,
            "radius check: first exact cross cancellation",
        )
        ck(
            cross.T * W * B == 2 * s.ones(r, 1) * y0 * B + wei.T * fres.T * B,
            "radius check: second exact cross cancellation",
        )
        M = WE.col_join(W)
        J = (eta * L).row_join(s.zeros(r)).col_join(cross.row_join(eta * L))
        Q = s.ones(2 * r, 1) * dy + J * M - J.T * M * B
        qe = s.ones(r, 1) * dy + eta * L * WE - eta * L.T * WE * B - cross.T * W * B
        ql = s.ones(r, 1) * dy + cross * WE + eta * L * W - eta * L.T * W * B
        ck(Q == qe.col_join(ql), "radius check: early/late block expansion of Q")
        ck(
            star(Q - p0.T * X) <= bq and p0 * M == -a * ellstar,
            "radius check: Q bound and count cancellation",
        )
        rm = s.zeros(r, r).row_join(wi)
        P = p0 + dr * rm + LX * ((Q - p0.T * X).T - X.T * dr * rm)
        ck(
            P * M == D and P.T * X == Q and star(P - p0) <= bp,
            "radius check: exact resets and P bound",
        )
        ck(
            min(cross) > 0 and max(P[:, :r]) < 0 and min(P[:, r:]) > 0,
            "radius check: coupling signs",
        )
        ck(
            min(-P[i, j] for i in range(X.rows - 1) for j in range(r)) > min(a) / 4,
            "radius check: parent margins",
        )
        ck(
            min(-P[-1, j] - z["c"] for j in range(r)) > parent.allowance,
            "radius check: endpoint margins",
        )
    print(
        f"  CHECKED radius-uniform identities/bounds at radii A_min, 2*A_min, 17*A_min for parent d={d}."
    )


def get_priority_ranks(order: int) -> dict[int, int]:
    """Returns priority rank r(i) in {0, ..., m_k-1} (0 = highest priority) for order k."""
    order_list = list(range(3))
    m = 3
    for d in range(2, order):
        r = d + 1
        g_idx = m
        controllers = [m + 1 + j for j in range(2 * r)]
        # Priority: inherited parent < c_{2r-1} < ... < c_0 < g
        order_list = order_list + list(reversed(controllers)) + [g_idx]
        m += 1 + 2 * r
    return {action: rank for rank, action in enumerate(order_list)}


def install_strict_zero_start_game(
    parent: Parent, q_start: int | None = None
) -> tuple[s.Matrix, s.Matrix, s.Matrix]:
    """Installs a single setup action + rational priority bias (the setup and bias lemmas)."""
    if q_start is None:
        q_start = parent.threshold
    m_k = parent.G.rows
    w = parent.order
    p_vec = s.Matrix([s.binomial(q_start, j) for j in range(w)])
    F = parent.R * p_vec
    D0 = 1
    for val in list(parent.G) + list(F):
        D0 = lcm(D0, int(R(val).q))
    ranks = get_priority_ranks(parent.order)
    b_vec = s.Matrix([R(m_k - 1 - ranks[i], 4 * m_k * D0) for i in range(m_k)])
    F_plus_b = F + b_vec
    F_star = F_plus_b + (1 - min(F_plus_b)) * s.ones(m_k, 1)
    A_hat = s.zeros(1, 1).row_join(-F_star.T).col_join(F_star.row_join(parent.G))
    ck(A_hat + A_hat.T == s.zeros(m_k + 1), "installed game skew-symmetric")
    ck(min(F_star) >= 1, "installed recurrent scores >= 1 after setup")
    return A_hat, F, F_star


def verify_unique_post_setup_decisions(
    A_hat: s.Matrix,
    parent: Parent | None = None,
    F_unperturbed: s.Matrix | None = None,
    num_steps: int = 64,
) -> list[int]:
    """Simulates simultaneous fictitious play from zero counts after playing setup at t=0,
    and optionally compares every step against the unperturbed fixed-priority clock process.
    """
    n = A_hat.rows
    u = A_hat[:, 0]
    played = []
    for t in range(1, num_steps + 1):
        max_score = max(u)
        maximizers = [i for i in range(n) if u[i] == max_score]
        ck(len(maximizers) == 1, f"strictly unique best response at t={t}")
        best = maximizers[0]
        ck(best >= 1, f"setup action 0 never re-played at t={t}")
        played.append(best - 1)
        u = u + A_hat[:, best]

    if parent is not None and F_unperturbed is not None:
        m_k = parent.G.rows
        ranks = get_priority_ranks(parent.order)
        u_unp = F_unperturbed.copy()
        unp_played = []
        for t in range(1, num_steps + 1):
            max_unp = max(u_unp)
            candidates = [i for i in range(m_k) if u_unp[i] == max_unp]
            best_unp = min(candidates, key=lambda i: ranks[i])
            unp_played.append(best_unp)
            u_unp = u_unp + parent.G[:, best_unp]
        ck(
            played == unp_played,
            "installed strict trajectory matches unperturbed fixed-priority trajectory",
        )

    return played


def verify_exposition():
    q, u, stride, c = s.symbols("q u stride c")
    phase = 9 * q + 18
    chi = q + 1
    ck(s.expand(chi.subs(q, q + 1) - chi) == 1, "RPS height increment")
    ck(
        s.expand(chi.subs(q, 2 * stride * q) - chi.subs(q, stride * q) + c)
        == stride * q + c,
        "first lifted height recurrence",
    )
    bundle = s.expand(
        s.summation(phase.subs(q, u), (u, stride * q, 2 * stride * q - 1))
    )
    ck(
        bundle == R(27, 2) * stride**2 * q**2 + R(27, 2) * stride * q,
        "exact RPS bundle length",
    )
    y = q * q / 2 + q + 4
    ck(
        s.expand(y - y.subs(q, q - 1)) == q + R(1, 2),
        "first reference-height polynomial",
    )
    T = s.symbols("T")
    ck(
        s.simplify(R(1, 2) + R(81, 2) / (12 * T + 27) - 2 * (T + 9) / (4 * T + 9)) == 0,
        "first parity correction",
    )
    print("CHECKED RPS-based exposition and exact first even-degree correction.")


def verify_named_identities():
    """Bounded symbolic regressions for polynomial identities."""
    q, theta, x = s.symbols("q theta x")
    binom = lambda z, j: (
        s.prod(z - k for k in range(j)) / factorial(j) if j >= 0 else s.S.Zero
    )
    for degree in range(9):
        ck(
            s.expand(binom(q + 1, degree) - binom(q, degree) - binom(q, degree - 1))
            == 0,
            f"Pascal polynomial identity, degree {degree}",
        )
        # Testing the monomial basis checks the expansion for every polynomial
        # of degree at most 8, by linearity, rather than at sampled phase values.
        coeffs = [
            sum(
                (-1) ** (j - h) * comb(j, h) * s.Integer(h) ** degree
                for h in range(j + 1)
            )
            for j in range(degree + 1)
        ]
        ck(
            s.expand(
                sum(coeffs[j] * binom(q, j) for j in range(degree + 1)) - q**degree
            )
            == 0,
            f"forward-difference expansion, degree {degree}",
        )
        ck(
            s.expand(
                sum(
                    comb(degree, j) * theta**j * (1 - theta) ** (degree - j)
                    for j in range(degree + 1)
                )
                - 1
            )
            == 0,
            f"Bernstein partition of unity, degree {degree}",
        )
        ck(
            s.expand(
                (q - 1) ** degree / factorial(degree)
                - sum(
                    (-1) ** (degree - j) * q**j / (factorial(degree - j) * factorial(j))
                    for j in range(degree + 1)
                )
            )
            == 0,
            f"scaled-monomial shift, degree {degree}",
        )
    for d in range(2, 10):
        modulus = s.Poly(x ** (2 * d + 1), x)
        trunc = lambda f: s.rem(s.Poly(f, x), modulus).as_expr()
        p = sum(
            R((-1) ** (j + 1), factorial(j)) * x ** (j - 1) for j in range(1, 2 * d + 1)
        )
        exponential = sum((-x) ** j / factorial(j) for j in range(2 * d + 1))
        ck(
            trunc(1 - exponential - x * p) == 0,
            f"finite exponential factorization, d={d}",
        )
        power, inverse = s.S.One, s.S.One
        for _ in range(1, 2 * d + 1):
            power = trunc(-power * (p - 1))
            inverse += power
        ck(trunc(p * inverse - 1) == 0, f"finite geometric inverse, d={d}")
    print(
        "CHECKED named polynomial identities in degrees 0..8; finite exponential/geometric identities for d=2..9."
    )


if __name__ == "__main__":
    import json
    from pathlib import Path

    parser = argparse.ArgumentParser(
        description="Verify the uniform RPS-based construction from d=2."
    )
    parser.add_argument("--max-order", type=int, default=5)
    args = parser.parse_args()
    ck(args.max_order >= 2, "max order at least two")
    verify_exposition()
    verify_named_identities()
    verify_cokernel_linear_algebra(9)
    started = time.time()
    cur = build_and_verify_rps_core()
    game, raw, _ = install_strict_zero_start_game(cur, cur.threshold)
    observed = verify_unique_post_setup_decisions(game, cur, raw, 64)
    expected = []
    q = 1
    while len(expected) < 64:
        for i in range(3):
            expected += [i] * (3 * q + 5 + i)
        q += 1
    ck(observed == expected[:64], "strict installed RPS initial word")
    results = [
        {"order": 2, "recurrent_actions": 3, "total_actions": 4, "strict_decisions": 64}
    ]
    print("CHECKED order 2: three recurrent actions, four including setup.", flush=True)
    for k in range(3, args.max_order + 1):
        tick = time.time()
        wit = lift_order(cur, verbose=True, plan_next=True)
        cert = verify_lift(wit)
        verify_radius_cancellations(cur)
        out = wit["output_parent"]
        n = out.G.rows + 1
        ck(n == (k + 1) ** 2 - 5, "uniform RPS action count")
        game, raw, _ = install_strict_zero_start_game(out, out.threshold)
        observed = verify_unique_post_setup_decisions(game, out, raw, 64)
        ck(all(i == out.b for i in observed), "initial controller run")
        if k == 3:
            c = wit["interface"]["c"]
            scale = (R(27) / (c - R(1, 2)) - 18) / 8
            ck(
                scale.q == 1 and c == 2 * (scale + 9) / (4 * scale + 9),
                "explicit first parity formula",
            )
        rec = {
            "order": k,
            "recurrent_actions": out.G.rows,
            "total_actions": n,
            "scale_bits": wit["scale_bits"],
            "radius_bits": wit["radius_bits"],
            "threshold": str(out.threshold),
            "strict_decisions": 64,
            "univariate_certificates": cert["univariate_count"],
            "uniform_certificates": cert["uniform_count"],
            "seconds": round(time.time() - tick, 3),
        }
        results.append(rec)
        print("CHECKED", json.dumps(rec), flush=True)
        cur = out
    report = {
        "status": "PASS",
        "orders": results,
        "elapsed_seconds": round(time.time() - started, 3),
        "scope": "Exact finite algebra and chronology certificates; 64 actual post-setup decisions per order; no complete lifted phase simulation or replacement for the all-order proof.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
