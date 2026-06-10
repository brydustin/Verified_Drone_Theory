# Strategy for Formalizing `det bigJ = - (5 * pi^8) / 3` in Isabelle

This note describes a practical Isabelle/HOL strategy for proving

```isabelle
lemma bigJ_det: "det bigJ = - (5 * pi^8) / 3"
```

for the concrete matrix

```isabelle
definition bigJ :: "real^12^12"
```

The key point is that one should **not** ask Isabelle to expand the raw `12 × 12` determinant directly.  The determinant has useful structure.  After permuting rows and columns, it becomes block triangular.  Then the determinant reduces to two `6 × 6` determinants, and those reduce further by elementary row operations and cofactor expansion.

The intended mathematical computation is:

\[
\det(\mathrm{bigJ}) = - \det(A)\det(D),
\]

where

\[
\det(A) = -\frac{\sqrt 3\,\pi^6}{18},
\qquad
\det(D) = -10\sqrt 3\,\pi^2.
\]

Thus

\[
\det(\mathrm{bigJ})
= -\left(-\frac{\sqrt 3\,\pi^6}{18}\right)
  \left(-10\sqrt 3\,\pi^2\right)
= -\frac{5\pi^8}{3}.
\]

---

## 1. Do not expand the original determinant directly

A proof like this is unlikely to be robust:

```isabelle
lemma bigJ_det: "det bigJ = - (5 * pi^8) / 3"
  unfolding bigJ_def
  by (simp add: field_simps) ring
```

The raw determinant has `12!` permutation terms in principle.  Even if Isabelle performs some simplification, this is the wrong proof shape.

Instead, formalize a sequence of determinant-preserving transformations.

---

## 2. Introduce abbreviations for `pi` and `sqrt 3`

In local proofs, use abbreviations:

```isabelle
let ?p = "pi :: real"
let ?s = "sqrt 3 :: real"
```

You will repeatedly need:

```isabelle
have s_sq: "?s * ?s = 3"
  by simp
```

Sometimes also useful:

```isabelle
have s_nonzero: "?s ≠ 0"
  by simp
```

For algebraic cleanup, the usual ending is:

```isabelle
by (simp add: s_sq field_simps power2_eq_square power3_eq_cube; ring)
```

or, when the goal is purely polynomial after clearing denominators:

```isabelle
by (simp add: s_sq field_simps power2_eq_square power3_eq_cube) ring
```

---

## 3. Permute rows and columns to expose block triangular structure

Use the row order

```text
1, 2, 3, 4, 7, 8, 5, 6, 9, 10, 11, 12
```

and the column order

```text
1, 3, 5, 7, 9, 11, 2, 4, 6, 8, 10, 12
```

In zero-based Isabelle indexing, these are

```text
rows: 0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11
cols: 0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11
```

Let the permuted matrix be `Jperm`.

Mathematically:

\[
J_{\mathrm{perm}} = P_r\, \mathrm{bigJ}\, P_c,
\]

where `P_r` permutes the rows and `P_c` permutes the columns.

After this permutation,

\[
J_{\mathrm{perm}}
= \begin{pmatrix}
A & 0 \\
C & D
\end{pmatrix}.
\]

Therefore

\[
\det(J_{\mathrm{perm}}) = \det(A)\det(D).
\]

The row permutation has sign `+1`.  It moves rows `7,8` above rows `5,6`, creating four inversions.

The column permutation has sign `-1`.  Moving the odd-numbered columns before the even-numbered columns creates

\[
1+2+3+4+5 = 15
\]

inversions.

Therefore

\[
\det(J_{\mathrm{perm}}) = -\det(\mathrm{bigJ}),
\]

so

\[
\det(\mathrm{bigJ}) = -\det(A)\det(D).
\]

### Isabelle implementation options

There are two reasonable ways to formalize the permutation step.

#### Option A: Define `Jperm` directly

This is the most practical option.

Define a new concrete matrix `Jperm` whose rows and columns are already ordered as above. Then prove:

```isabelle
lemma det_bigJ_eq_neg_det_Jperm:
  "det bigJ = - det Jperm"
```

This can be proved either by a permutation determinant lemma, or by two applications of row/column swap lemmas.

For row swaps, use repeated determinant swap facts, such as facts of the shape:

```isabelle
det_permute_rows
 det_permute_columns
 det_swap_rows
 det_swap_columns
```

The exact theorem names depend on the imported library. Search with:

```isabelle
find_theorems det permute
find_theorems det swap row
find_theorems det swap column
find_theorems det "Fun.swap"
```

If permutation lemmas are awkward for Cartesian matrices, use direct swap steps.  For the row permutation, you only need to move rows `6,7` into positions `4,5`.  That can be done by adjacent swaps.  There are four adjacent swaps total, hence sign `+1`.

For the column permutation, move columns `0,2,4,6,8,10` to the front.  This produces fifteen adjacent swaps, hence sign `-1`.

#### Option B: Avoid formal permutation matrices

Instead of defining `Jperm = P_r * bigJ * P_c`, prove directly that `Jperm` is obtained from `bigJ` by a known sequence of swaps.

This is usually easier for a concrete proof:

```isabelle
have det_after_row_swaps:
  "det Jrow = det bigJ"
  ...

have det_after_col_swaps:
  "det Jperm = - det Jrow"
  ...

hence det_relation:
  "det bigJ = - det Jperm"
  by simp
```

The benefit is that every swap proof is simple and local.

---

## 4. Define the block matrices `A`, `C`, and `D`

After the row and column permutation, define the two relevant blocks explicitly.

Use:

```isabelle
definition A :: "real^6^6" where
  "A = vector [ ... ]"

 definition D :: "real^6^6" where
  "D = vector [ ... ]"
```

The block `C` does not matter for the determinant, but `Jperm` has the form

\[
\begin{pmatrix}
A & 0 \\
C & D
\end{pmatrix}.
\]

You can define `C` if it helps state the block decomposition, but it is not necessary if you prove the block determinant formula directly for the concrete `Jperm`.

The upper-right block must be zero.  This is the key structural fact.

Prove a lemma:

```isabelle
lemma Jperm_block_lower_triangular:
  "Jperm = block_lower_triangular A C D"
```

or, more concretely, if you have a block-matrix constructor available:

```isabelle
lemma Jperm_eq_block:
  "Jperm = four_block_mat A 0 C D"
```

If no convenient block constructor exists for Cartesian matrices, state the determinant relation directly:

```isabelle
lemma det_Jperm:
  "det Jperm = det A * det D"
```

and prove it by using the determinant formula for block triangular matrices, or by cofactor expansion along the zero upper-right block.

Search for available block determinant facts:

```isabelle
find_theorems det block
find_theorems det triangular
find_theorems det matrix block
```

If no theorem is available, the fallback is to prove the concrete `12 × 12` determinant of `Jperm` by expanding along the six zero-heavy columns/rows.  This is still much easier than the original determinant because the upper-right block is zero.

---

## 5. The matrix `A`

With `p = pi` and `s = sqrt 3`, the first block is

\[
A=\begin{pmatrix}
0&-s/2&-s/2&0&s/2&s/2\\
-1&-1/2&1/2&1&1/2&-1/2\\
1&1/2-ps/6&-1/2-ps/3&-1&-1/2+2ps/3&1/2+5ps/6\\
0&-s/2-p/6&-s/2+p/3&p&s/2+2p/3&s/2-5p/6\\
0&p/3-p^2s/18&-2p/3-2p^2s/9&-2p&-4p/3+8p^2s/9&5p/3+25p^2s/18\\
0&-ps/3-p^2/18&-2ps/3+2p^2/9&p^2&4ps/3+8p^2/9&5ps/3-25p^2/18
\end{pmatrix}.
\]

In Isabelle, define it explicitly:

```isabelle
definition A :: "real^6^6" where
  "A = vector
    [ vector [0, - sqrt 3 / 2, - sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [-1, -1/2, 1/2, 1, 1/2, -1/2],
      vector [1, 1/2 - pi * sqrt 3 / 6, -1/2 - pi * sqrt 3 / 3,
              -1, -1/2 + 2 * pi * sqrt 3 / 3, 1/2 + 5 * pi * sqrt 3 / 6],
      vector [0, -sqrt 3 / 2 - pi / 6, -sqrt 3 / 2 + pi / 3,
              pi, sqrt 3 / 2 + 2 * pi / 3, sqrt 3 / 2 - 5 * pi / 6],
      vector [0, pi / 3 - pi^2 * sqrt 3 / 18,
              -2 * pi / 3 - 2 * pi^2 * sqrt 3 / 9,
              -2 * pi, -4 * pi / 3 + 8 * pi^2 * sqrt 3 / 9,
              5 * pi / 3 + 25 * pi^2 * sqrt 3 / 18],
      vector [0, -pi * sqrt 3 / 3 - pi^2 / 18,
              -2 * pi * sqrt 3 / 3 + 2 * pi^2 / 9,
              pi^2, 4 * pi * sqrt 3 / 3 + 8 * pi^2 / 9,
              5 * pi * sqrt 3 / 3 - 25 * pi^2 / 18] ]"
```

### Row operations for `A`

Use determinant-preserving row additions:

```text
R3 <- R3 + R2
R4 <- R4 - R1
```

using one-based row numbering inside this explanation.

In zero-based row numbering:

```text
row 2 <- row 2 + row 1
row 3 <- row 3 - row 0
```

These operations do not change determinant.

After that, rows `3` and `4` contain a factor `p`.

The new rows are:

\[
R_3 = p(0,-s/6,-s/3,0,2s/3,5s/6),
\]

\[
R_4 = p(0,-1/6,1/3,1,2/3,-5/6).
\]

The last two rows have the form

\[
R_5 = pU + p^2V,
\qquad
R_6 = pW + p^2Z,
\]

where

\[
U = -2R_4/p,
\qquad
W = 2R_3/p.
\]

So, after extracting one factor of `p` from rows `3` and `4`, do:

```text
R5 <- R5 + 2 R4
R6 <- R6 - 2 R3
```

These remove the linear-in-`p` parts and leave rows with another factor of `p`.

Altogether, this exposes six powers of `p`:

\[
\det(A)=p^6\det(B).
\]

The resulting constant matrix is

\[
B=\begin{pmatrix}
0&-s/2&-s/2&0&s/2&s/2\\
-1&-1/2&1/2&1&1/2&-1/2\\
0&-s/6&-s/3&0&2s/3&5s/6\\
0&-1/6&1/3&1&2/3&-5/6\\
0&-s/18&-2s/9&0&8s/9&25s/18\\
0&-1/18&2/9&1&8/9&-25/18
\end{pmatrix}.
\]

Then prove:

```isabelle
lemma det_B: "det B = - sqrt 3 / 18"
```

This is a small `6 × 6` determinant with no `pi`. It should be manageable by cofactor expansion and `ring`.

Then prove:

```isabelle
lemma det_A: "det A = - sqrt 3 * pi^6 / 18"
```

using the row-operation chain and `det_B`.

### Recommended Isabelle lemma breakdown for `A`

Use intermediate matrices:

```isabelle
definition A1 :: "real^6^6" where ...
definition A2 :: "real^6^6" where ...
definition B  :: "real^6^6" where ...
```

Prove:

```isabelle
lemma det_A_eq_det_A1:
  "det A = det A1"
```

```isabelle
lemma det_A1_eq_pi2_det_A2:
  "det A1 = pi^2 * det A2"
```

```isabelle
lemma det_A2_eq_pi4_det_B:
  "det A2 = pi^4 * det B"
```

or simply:

```isabelle
lemma det_A_eq_pi6_det_B:
  "det A = pi^6 * det B"
```

Then:

```isabelle
lemma det_A:
  "det A = - sqrt 3 * pi^6 / 18"
  using det_A_eq_pi6_det_B det_B
  by (simp add: field_simps)
```

It is usually easier to prove row-operation lemmas one matrix at a time than to prove the entire relation in one calculation.

---

## 6. The matrix `D`

The lower-right block is

\[
D=\begin{pmatrix}
1&1/2&-1/2&-1&-1/2&1/2\\
0&-s/2&-s/2&0&s/2&s/2\\
0&p/6&-p/3&-p&-2p/3&5p/6\\
0&-ps/6&-ps/3&0&2ps/3&5ps/6\\
4&2&0&0&-2&2\\
0&-2s&0&0&2s&2s
\end{pmatrix}.
\]

In Isabelle:

```isabelle
definition D :: "real^6^6" where
  "D = vector
    [ vector [1, 1/2, -1/2, -1, -1/2, 1/2],
      vector [0, -sqrt 3 / 2, -sqrt 3 / 2, 0, sqrt 3 / 2, sqrt 3 / 2],
      vector [0, pi / 6, -pi / 3, -pi, -2 * pi / 3, 5 * pi / 6],
      vector [0, -pi * sqrt 3 / 6, -pi * sqrt 3 / 3, 0,
              2 * pi * sqrt 3 / 3, 5 * pi * sqrt 3 / 6],
      vector [4, 2, 0, 0, -2, 2],
      vector [0, -2 * sqrt 3, 0, 0, 2 * sqrt 3, 2 * sqrt 3] ]"
```

Rows `3` and `4` have a factor of `pi`, so:

\[
\det(D)=\pi^2\det(E).
\]

The constant matrix is

\[
E=\begin{pmatrix}
1&1/2&-1/2&-1&-1/2&1/2\\
0&-s/2&-s/2&0&s/2&s/2\\
0&1/6&-1/3&-1&-2/3&5/6\\
0&-s/6&-s/3&0&2s/3&5s/6\\
4&2&0&0&-2&2\\
0&-2s&0&0&2s&2s
\end{pmatrix}.
\]

Then simplify by row additions:

```text
R5 <- R5 - 4 R1
R6 <- R6 - 4 R2
```

This preserves determinant and gives

\[
E' =
\begin{pmatrix}
1&1/2&-1/2&-1&-1/2&1/2\\
0&-s/2&-s/2&0&s/2&s/2\\
0&1/6&-1/3&-1&-2/3&5/6\\
0&-s/6&-s/3&0&2s/3&5s/6\\
0&0&2&4&0&0\\
0&0&2s&0&0&0
\end{pmatrix}.
\]

Expand along the last row. The only nonzero entry is `2s` in column `3` in one-based numbering. Its cofactor sign is `-1`, so

\[
\det(E') = -2s \det(F).
\]

Then expand along the last row of `F`; the only nonzero entry is `4`, with positive sign. This gives

\[
\det(E') = -8s \det(G).
\]

where

\[
G=\begin{pmatrix}
1&1/2&-1/2&1/2\\
0&-s/2&s/2&s/2\\
0&1/6&-2/3&5/6\\
0&-s/6&2s/3&5s/6
\end{pmatrix}.
\]

Prove:

```isabelle
lemma det_G: "det G = 5 / 4"
```

Then:

\[
\det(E) = -8s\cdot\frac54 = -10s.
\]

Therefore:

\[
\det(D)=\pi^2\det(E)=-10s\pi^2.
\]

Recommended Isabelle lemmas:

```isabelle
lemma det_D_eq_pi2_det_E:
  "det D = pi^2 * det E"
```

```isabelle
lemma det_E_eq_det_Eprime:
  "det E = det Eprime"
```

```isabelle
lemma det_Eprime:
  "det Eprime = -10 * sqrt 3"
```

```isabelle
lemma det_D:
  "det D = -10 * sqrt 3 * pi^2"
```

---

## 7. Row-operation lemmas you will want

For Cartesian matrices, it may be convenient to prove your own concrete row operation lemmas if library facts are awkward.

You want facts like:

### Row replacement does not change determinant

If `M'` is obtained from `M` by replacing row `i` with row `i + c * row j`, where `i ≠ j`, then

```isabelle
det M' = det M
```

Search first:

```isabelle
find_theorems det row_add
find_theorems det "row"
find_theorems det "replace"
find_theorems det "vec_lambda"
```

If needed, prove a specialized lemma using multilinearity of determinant in rows.

For concrete matrices, an easier fallback is to define the row-modified matrix explicitly and prove the determinant equality by expansion, because the matrices are only `6 × 6`.

### Scaling a row scales determinant

If row `i` is multiplied by `c`, then the determinant is multiplied by `c`.

You will use this in reverse: if a row has an obvious factor of `pi`, pull it out.

Search:

```isabelle
find_theorems det row scale
find_theorems det mult_row
find_theorems det "*s"
```

Again, for concrete `6 × 6` matrices, the fallback is to define the scaled matrix explicitly and prove:

```isabelle
lemma det_A1_eq_pi2_det_A2:
  "det A1 = pi^2 * det A2"
  unfolding A1_def A2_def
  by (simp add: field_simps power2_eq_square; ring)
```

This is much easier than expanding the original `12 × 12` determinant.

---

## 8. Cofactor expansion for the small determinants

The determinants of `B`, `G`, and the simplified `Eprime` are good candidates for cofactor expansion.

Search theorem names:

```isabelle
find_theorems det expansion
find_theorems det cofactor
find_theorems name:det name:row
find_theorems name:det name:column
```

If using HOL-Analysis Cartesian determinants, the expansion facts may involve finite sums over the index type.  For a concrete dimension like `real^6^6`, it may be easier to use `simp` after unfolding the determinant of a small matrix.

Recommended final small determinant proofs:

```isabelle
lemma det_B: "det B = - sqrt 3 / 18"
  unfolding B_def
  by (simp add: field_simps power2_eq_square; ring)
```

```isabelle
lemma det_G: "det G = 5 / 4"
  unfolding G_def
  by (simp add: field_simps power2_eq_square; ring)
```

If these are still slow, expand along sparse rows/columns first.

---

## 9. Final theorem structure

The final proof should look like this:

```isabelle
lemma bigJ_det: "det bigJ = - (5 * pi^8) / 3"
proof -
  have s_sq: "(sqrt 3 :: real) * sqrt 3 = 3"
    by simp

  have perm: "det bigJ = - det Jperm"
    using det_bigJ_eq_neg_det_Jperm .

  have block: "det Jperm = det A * det D"
    using det_Jperm_block .

  have A_det: "det A = - sqrt 3 * pi^6 / 18"
    using det_A .

  have D_det: "det D = -10 * sqrt 3 * pi^2"
    using det_D .

  show ?thesis
    using perm block A_det D_det s_sq
    by (simp add: field_simps power2_eq_square power_add)
qed
```

You may need to help the final algebra with:

```isabelle
by (simp add: field_simps power2_eq_square power_add)
   ring
```

or:

```isabelle
by (simp add: s_sq field_simps power2_eq_square power_add; ring)
```

---

## 10. Suggested order of implementation

Do not start with the final theorem.  Build from the bottom up.

Recommended order:

1. Define `A`, `B`.
2. Prove `det_B`.
3. Prove `det_A = pi^6 * det B`.
4. Conclude `det_A`.
5. Define `D`, `E`, `Eprime`, `G`.
6. Prove `det_G`.
7. Prove `det_Eprime = -10 * sqrt 3`.
8. Prove `det_D = -10 * sqrt 3 * pi^2`.
9. Define `Jperm`.
10. Prove `det Jperm = det A * det D`.
11. Prove `det bigJ = - det Jperm`.
12. Combine everything.

This approach avoids overwhelming Isabelle with a large determinant and gives many small, debuggable lemmas.

---

## 11. Practical fallback strategy

If the row-operation lemmas become painful, use a more computational but still structured route:

* Define each intermediate matrix explicitly.
* Prove determinant equalities between consecutive matrices using `simp` and `ring`.
* Because the matrices are `6 × 6`, this is much more likely to terminate than the original `12 × 12` determinant.

For example:

```isabelle
lemma det_A_eq_pi6_det_B:
  "det A = pi^6 * det B"
  unfolding A_def B_def
  by (simp add: field_simps power2_eq_square; ring)
```

If this times out, split it further:

```isabelle
lemma det_A_eq_det_A1:
  "det A = det A1"
  unfolding A_def A1_def
  by (simp add: field_simps power2_eq_square; ring)

lemma det_A1_eq_pi2_det_A2:
  "det A1 = pi^2 * det A2"
  unfolding A1_def A2_def
  by (simp add: field_simps power2_eq_square; ring)

lemma det_A2_eq_pi4_det_B:
  "det A2 = pi^4 * det B"
  unfolding A2_def B_def
  by (simp add: field_simps power2_eq_square; ring)
```

This is less elegant than using general determinant lemmas, but it is often the fastest path to a working Isabelle proof.

---

## 12. Key mathematical identities to preserve

The whole proof rests on these identities:

\[
\det(\mathrm{bigJ}) = -\det(J_{\mathrm{perm}}),
\]

\[
\det(J_{\mathrm{perm}})=\det(A)\det(D),
\]

\[
\det(A)=\pi^6\det(B),
\]

\[
\det(B)=-\frac{\sqrt 3}{18},
\]

\[
\det(D)=\pi^2\det(E),
\]

\[
\det(E)=-10\sqrt 3.
\]

Combining:

\[
\det(\mathrm{bigJ})
= -\left(\pi^6\left(-\frac{\sqrt 3}{18}\right)\right)
   \left(\pi^2(-10\sqrt 3)\right)
= -\frac{5\pi^8}{3}.
\]

