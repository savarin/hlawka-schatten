# Dimension-independent Hlawka constants for Schatten norms

## Target

Prove that for every Schatten exponent p > 1, there exists a finite
constant C_p such that for all linear maps X, Y, Z between finite-dimensional
complex inner product spaces of any dimension,

  N(X) + N(Y) + N(Z) - N(X+Y+Z) <= C_p [N(X)+N(Y)-N(X+Y) + N(X)+N(Z)-N(X+Z) + N(Y)+N(Z)-N(Y+Z)]

where N is the Schatten p-norm. Prove that no such constant exists at the
trace norm (p = 1, 2 x 2 operators) or the operator norm (p = infinity,
3 x 3 matrices).

## Proof route

**Scalar comparison.** The scalar power potential t -> |t|^p has Bregman
divergence beta_p(a,b). Dividing by the squared distance of the scalar
Mazur images psi_p(a) = sgn(a)|a|^{p/2} gives a quotient that extends
continuously and positively to the compactified real line. By compactness,
there exist 0 < m_p <= M_p with

  m_p |psi_p(a) - psi_p(b)|^2 <= beta_p(a,b) <= M_p |psi_p(a) - psi_p(b)|^2.

**Spectral lift.** For two Hermitian operators with eigenbases {e_i}, {f_j},
the Bregman and squared-Mazur quantities decompose as double sums weighted
by |<e_i, f_j>|^2. These weights are nonneg with rows and columns summing
to one, so the scalar two-sided estimate lifts without changing m_p, M_p.

**Hermitian dilation.** Every rectangular operator T embeds as the
off-diagonal block of a Hermitian operator. The odd functional calculus
extracts the rectangular Mazur map, while the even functional calculus
identifies its Schatten-2 power with the original Schatten-p power.

**Variational comparison.** On the Schatten power sphere, weighted Bregman
objectives attain the triple/pair deficits; weighted squared Hilbert
distances attain twice the corresponding Schatten-2 gaps. Comparing minima
gives a two-sided inequality between deficits.

**Radial Mazur map.** A radial (non-spherical) version of the Mazur map
sends each operator to a Hilbert vector of the same individual norm,
removing the sphere normalization. Hilbert Hlawka bounds the mapped triple
deficit by the mapped pair deficits. Combining the triple upper estimate
with the three pair lower estimates yields the constant M_p/m_p.

**Trace norm endpoint (p = 1).** A family of rank-one projectors
parameterized by s has triple deficit 4s^2 and pair-deficit sum at most
8s^4; choosing s after a proposed constant gives a contradiction. The
calculation uses the exact 2D identity ||T||_1^2 = ||T||_2^2 + 2 normDet(T).

**Operator norm endpoint (p = infinity).** Three signed diagonal 3 x 3
matrices have all three pair deficits equal to zero but positive triple
deficit.

## Key lemmas

- Compactness of the scalar Bregman-to-Mazur ratio on the extended real
  line gives the constants m_p, M_p.
- The spectral overlap matrix has nonneg entries summing to one along rows
  and columns — the convexity engine for the lift.
- Hermitian dilation is norm-preserving and interacts cleanly with odd/even
  functional calculus.
- The Hilbert Hlawka inequality (triple deficit <= sum of pair deficits in
  inner product spaces) is the final comparison tool.
- The 2D trace-norm identity links the Schatten 1-norm to the Frobenius
  norm plus normalized determinant.

## Pitfalls

- The odd functional calculus (sgn composed with the absolute value power)
  must respect the block structure of the dilation; applying it naively to
  the full Hermitian operator mixes the diagonal and off-diagonal blocks.
- The radial Mazur map must preserve individual norms without sphere
  normalization — the sphere version introduces denominators that break
  the Hlawka application.
- The exact 2D trace-norm identity (||T||_1^2 = ||T||_2^2 + 2|det T|) is
  specific to 2x2 matrices; in higher dimensions the p=1 obstruction
  follows by embedding the 2x2 family via zero-padding.
- The p = infinity witness uses 3x3 diagonal matrices because every
  two-dimensional real normed space satisfies Hlawka; three diagonal
  coordinates are the minimum needed for a counterexample.

## Sharp diagonal construction for real p ≥ 256

The separate `ConstructionDiagonal` boundary determines the sharp constant
for complex diagonal Schatten norms. It holds in every finite dimension and
is sharp in every dimension at least three. It specifies the constant as
the maximum cyclic ratio over `[1/2, 2]` and proves attainment there. See
[proof/diagonal-construction.md](proof/diagonal-construction.md) for the
formula, module map, and exact estimates used in Lean.

**Three-coordinate reduction.** Fix the three pair power sums and vary
nonnegative coordinate weights. The positive part of the desired inequality
is concave in those weights. A compact minimization argument produces a
minimizer supported on at most three coordinates.

**Relabeling and scalar confinement.** Permute the zero-sum quadruple to
make the total norm the largest, then normalize the sum of singleton norms
to one. The weighted scalar convexity inequality bounds the pair norm sum
in terms of the total norm. The explicit cyclic witness `t = p^(-1/p)`
forces a strict counterexample to have total norm below `53/150`, singleton
norms close to `1/3`, and small pair deficits.

**Joint coordinate geometry.** Each nearly saturated pair chooses a
coordinate. Two pairs cannot choose the same coordinate: their shared
vector fixes the sign, and the total norm would be too large. After
reorienting coordinates and scaling by three, the entire triple lies in the
entrywise radius-`19/100` box around `J - 2I`.

**Convexity and averaging.** The singleton and total norm Hessians jointly
control independent column rescalings. Their lower bound dominates the
three pair Hessians throughout the box for every real `p ≥ 256`. The sharp
deficit is therefore convex there. Averaging simultaneous permutations of
columns and coordinates yields a cyclic triple whose bound follows from
the definition of the constant. This excludes the original counterexample.

**Complex and diagonal transfer.** Real circle projections reproduce each
complex norm power up to the same positive factor. Finite convex
combinations satisfy the real bound, and continuity passes it to their
closed convex hull, which contains the circle integral. Finally, the
existing spectral functional-calculus trace identity proves that a diagonal
operator's singular-value power sum equals its coordinate power sum.

**Sharpness and attainment.** The explicit three-coordinate cyclic vectors
have the stated ratio and embed into every larger dimension. Their ratio
has positive denominator and is continuous on `[1/2, 2]`, so it attains a
maximum. No classification of all maximizers is asserted.
