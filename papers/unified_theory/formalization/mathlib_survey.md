# mathlib survey for the PZG-BEDC base layer

本文件只记录可复用的 mathlib declaration。路径均指向
`papers/unified_theory/lean4/.lake/packages/mathlib/Mathlib/` 下的源文件。

## 1. Golden ratio `φ` / `ψ`

核心文件：`NumberTheory/Real/GoldenRatio.lean`

| declaration | signature | path | 用途 |
|---|---|---|---|
| `Real.goldenRatio` | `Real.goldenRatio : ℝ` | `NumberTheory/Real/GoldenRatio.lean` | 定义 `φ = (1 + √5) / 2`，并通过 scoped notation `φ` 使用。 |
| `Real.goldenConj` | `Real.goldenConj : ℝ` | `NumberTheory/Real/GoldenRatio.lean` | 定义 `ψ = (1 - √5) / 2`，并通过 scoped notation `ψ` 使用。 |
| `Real.inv_goldenRatio` | `φ⁻¹ = -ψ` | `NumberTheory/Real/GoldenRatio.lean` | 把 `φ` 的倒数改写成 `-ψ`。 |
| `Real.inv_goldenConj` | `ψ⁻¹ = -φ` | `NumberTheory/Real/GoldenRatio.lean` | 把 `ψ` 的倒数改写成 `-φ`。 |
| `Real.goldenRatio_mul_goldenConj` | `φ * ψ = -1` | `NumberTheory/Real/GoldenRatio.lean` | 证明两根乘积为 `-1`。 |
| `Real.goldenConj_mul_goldenRatio` | `ψ * φ = -1` | `NumberTheory/Real/GoldenRatio.lean` | 乘积换序版本，便于 `simp`。 |
| `Real.goldenRatio_add_goldenConj` | `φ + ψ = 1` | `NumberTheory/Real/GoldenRatio.lean` | 证明两根和为 `1`。 |
| `Real.one_sub_goldenConj` | `1 - φ = ψ` | `NumberTheory/Real/GoldenRatio.lean` | 从 `φ + ψ = 1` 解出 `ψ`。 |
| `Real.one_sub_goldenRatio` | `1 - ψ = φ` | `NumberTheory/Real/GoldenRatio.lean` | 从 `φ + ψ = 1` 解出 `φ`。 |
| `Real.goldenRatio_sub_goldenConj` | `φ - ψ = √5` | `NumberTheory/Real/GoldenRatio.lean` | Binet 分母 `√5` 的直接来源。 |
| `Real.goldenRatio_pow_sub_goldenRatio_pow` | `(n : ℕ) : φ ^ (n + 2) - φ ^ (n + 1) = φ ^ n` | `NumberTheory/Real/GoldenRatio.lean` | `φ` 幂满足 Fibonacci characteristic equation。 |
| `Real.goldenRatio_sq` | `φ ^ 2 = φ + 1` | `NumberTheory/Real/GoldenRatio.lean` | 主要平方化简；兼容 alias `gold_sq` 也存在。 |
| `Real.goldenConj_sq` | `ψ ^ 2 = ψ + 1` | `NumberTheory/Real/GoldenRatio.lean` | `ψ` 的平方化简；兼容 alias `goldConj_sq` 也存在。 |
| `Real.goldenRatio_pos` | `0 < φ` | `NumberTheory/Real/GoldenRatio.lean` | 处理除法、正性和不等式。 |
| `Real.goldenRatio_ne_zero` | `φ ≠ 0` | `NumberTheory/Real/GoldenRatio.lean` | `field`/除法 proof 的非零条件。 |
| `Real.one_lt_goldenRatio` | `1 < φ` | `NumberTheory/Real/GoldenRatio.lean` | 增长性和极限估计。 |
| `Real.goldenRatio_lt_two` | `φ < 2` | `NumberTheory/Real/GoldenRatio.lean` | 粗上界。 |
| `Real.goldenConj_neg` | `ψ < 0` | `NumberTheory/Real/GoldenRatio.lean` | 控制 conjugate 项符号。 |
| `Real.goldenConj_ne_zero` | `ψ ≠ 0` | `NumberTheory/Real/GoldenRatio.lean` | `ψ` 除法和幂改写的非零条件。 |
| `Real.neg_one_lt_goldenConj` | `-1 < ψ` | `NumberTheory/Real/GoldenRatio.lean` | 控制 `|ψ| < 1` 类估计。 |
| `Real.goldenRatio_irrational` | `Irrational φ` | `NumberTheory/Real/GoldenRatio.lean` | `φ` irrationality 可直接引用。 |
| `Real.goldenConj_irrational` | `Irrational ψ` | `NumberTheory/Real/GoldenRatio.lean` | `ψ` irrationality 可直接引用。 |

Fibonacci bridge in the same file:

| declaration | signature | path | 用途 |
|---|---|---|---|
| `Real.fibRec` | `{α : Type u} [CommSemiring α] : LinearRecurrence α` | `NumberTheory/Real/GoldenRatio.lean` | Fibonacci recurrence as a `LinearRecurrence` with coefficients `![1, 1]`。 |
| `Real.fibRec_charPoly_eq` | `{β : Type u} [CommRing β] : Real.fibRec.charPoly = Polynomial.X ^ 2 - (Polynomial.X + 1)` | `NumberTheory/Real/GoldenRatio.lean` | characteristic polynomial bridge。 |
| `Real.fib_isSol_fibRec` | `{α : Type u} [CommSemiring α] : Real.fibRec.IsSolution fun x => ↑(Nat.fib x)` | `NumberTheory/Real/GoldenRatio.lean` | `Nat.fib` satisfies `fibRec`。 |
| `Real.geom_goldenRatio_isSol_fibRec` | `Real.fibRec.IsSolution fun x => φ ^ x` | `NumberTheory/Real/GoldenRatio.lean` | `φ^n` is a recurrence solution。 |
| `Real.geom_goldenConj_isSol_fibRec` | `Real.fibRec.IsSolution fun x => ψ ^ x` | `NumberTheory/Real/GoldenRatio.lean` | `ψ^n` is a recurrence solution。 |
| `Real.coe_fib_eq'` | `(fun n => ↑(Nat.fib n)) = fun n => (φ ^ n - ψ ^ n) / √5` | `NumberTheory/Real/GoldenRatio.lean` | Binet formula as function equality。 |
| `Real.coe_fib_eq` | `(n : ℕ) : ↑(Nat.fib n) = (φ ^ n - ψ ^ n) / √5` | `NumberTheory/Real/GoldenRatio.lean` | Binet formula for `Nat.fib` at one index。 |
| `Real.coe_intFib_eq` | `(n : ℤ) : ↑(Int.fib n) = (φ ^ n - ψ ^ n) / √5` | `NumberTheory/Real/GoldenRatio.lean` | integer-index Binet formula。 |
| `Real.fib_succ_sub_goldenRatio_mul_fib` | `(n : ℕ) : Nat.fib (n + 1) - φ * Nat.fib n = ψ ^ n` | `NumberTheory/Real/GoldenRatio.lean` | isolates the `ψ^n` error term。 |
| `Real.goldenConj_mul_fib_succ_add_fib` | `(n : ℕ) : ψ * Nat.fib (n + 1) + Nat.fib n = ψ ^ (n + 1)` | `NumberTheory/Real/GoldenRatio.lean` | expresses `ψ` powers by Fibonacci coefficients。 |
| `Real.goldenRatio_mul_fib_succ_add_fib` | `(n : ℕ) : φ * Nat.fib (n + 1) + Nat.fib n = φ ^ (n + 1)` | `NumberTheory/Real/GoldenRatio.lean` | expresses `φ` powers by Fibonacci coefficients。 |
| `Real.fib_succ_sub_goldenConj_mul_fib` | `(n : ℕ) : Nat.fib (n + 1) - ψ * Nat.fib n = φ ^ n` | `NumberTheory/Real/GoldenRatio.lean` | isolates the `φ^n` term from `ψ` side。 |

Limit bridge:

| declaration | signature | path | 用途 |
|---|---|---|---|
| `tendsto_fib_succ_div_fib_atTop` | `Filter.Tendsto (fun n => ↑(Nat.fib (n + 1)) / ↑(Nat.fib n)) Filter.atTop (nhds φ)` | `Analysis/SpecificLimits/Fibonacci.lean` | consecutive Fibonacci ratio tends to `φ`。 |
| `tendsto_fib_div_fib_succ_atTop` | `Filter.Tendsto (fun n => ↑(Nat.fib n) / ↑(Nat.fib (n + 1))) Filter.atTop (nhds (-ψ))` | `Analysis/SpecificLimits/Fibonacci.lean` | inverse ratio tends to `-ψ = φ⁻¹`。 |

## 2. Fibonacci

核心文件：`Data/Nat/Fib/Basic.lean`

| declaration | signature | path | 用途 |
|---|---|---|---|
| `Nat.fib` | `(n : ℕ) : ℕ` | `Data/Nat/Fib/Basic.lean` | Fibonacci sequence with `F₀ = 0`, `F₁ = 1`。 |
| `Nat.fib_zero` | `Nat.fib 0 = 0` | `Data/Nat/Fib/Basic.lean` | base case。 |
| `Nat.fib_one` | `Nat.fib 1 = 1` | `Data/Nat/Fib/Basic.lean` | base case。 |
| `Nat.fib_two` | `Nat.fib 2 = 1` | `Data/Nat/Fib/Basic.lean` | small numeral simplification。 |
| `Nat.fib_add_two` | `{n : ℕ} : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1)` | `Data/Nat/Fib/Basic.lean` | main recurrence。 |
| `Nat.fib_add_one` | `{n : ℕ} : n ≠ 0 → Nat.fib (n + 1) = Nat.fib (n - 1) + Nat.fib n` | `Data/Nat/Fib/Basic.lean` | predecessor form of recurrence。 |
| `Nat.fib_le_fib_succ` | `{n : ℕ} : Nat.fib n ≤ Nat.fib (n + 1)` | `Data/Nat/Fib/Basic.lean` | monotonicity step。 |
| `Nat.fib_mono` | `Monotone Nat.fib` | `Data/Nat/Fib/Basic.lean` | monotone map API。 |
| `Nat.fib_eq_zero` | `{n : ℕ} : Nat.fib n = 0 ↔ n = 0` | `Data/Nat/Fib/Basic.lean` | positivity/nonzero bridge。 |
| `Nat.fib_pos` | `{n : ℕ} : 0 < Nat.fib n ↔ 0 < n` | `Data/Nat/Fib/Basic.lean` | positivity bridge。 |
| `Nat.fib_lt_fib_succ` | `{n : ℕ} (hn : 2 ≤ n) : Nat.fib n < Nat.fib (n + 1)` | `Data/Nat/Fib/Basic.lean` | strict growth after index `2`。 |
| `Nat.fib_add_two_strictMono` | `StrictMono fun n => Nat.fib (n + 2)` | `Data/Nat/Fib/Basic.lean` | strict monotonicity for shifted sequence。 |
| `Nat.fib_strictMonoOn` | `StrictMonoOn Nat.fib (Set.Ici 2)` | `Data/Nat/Fib/Basic.lean` | strict monotonicity on indices `≥ 2`。 |
| `Nat.fib_lt_fib` | `{m : ℕ} (hm : 2 ≤ m) {n : ℕ} : Nat.fib m < Nat.fib n ↔ m < n` | `Data/Nat/Fib/Basic.lean` | compare indices through Fibonacci values。 |
| `Nat.fib_coprime_fib_succ` | `(n : ℕ) : (Nat.fib n).Coprime (Nat.fib (n + 1))` | `Data/Nat/Fib/Basic.lean` | adjacent Fibonacci numbers are coprime。 |
| `Nat.fib_add` | `(m n : ℕ) : Nat.fib (m + n + 1) = Nat.fib m * Nat.fib n + Nat.fib (m + 1) * Nat.fib (n + 1)` | `Data/Nat/Fib/Basic.lean` | addition formula。 |
| `Nat.fib_two_mul` | `(n : ℕ) : Nat.fib (2 * n) = Nat.fib n * (2 * Nat.fib (n + 1) - Nat.fib n)` | `Data/Nat/Fib/Basic.lean` | doubling formula。 |
| `Nat.fib_two_mul_add_one` | `(n : ℕ) : Nat.fib (2 * n + 1) = Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2` | `Data/Nat/Fib/Basic.lean` | odd doubling formula。 |
| `Nat.fib_gcd` | `(m n : ℕ) : Nat.fib (m.gcd n) = (Nat.fib m).gcd (Nat.fib n)` | `Data/Nat/Fib/Basic.lean` | strong divisibility sequence theorem。 |
| `Nat.fib_dvd` | `(m n : ℕ) (h : m ∣ n) : Nat.fib m ∣ Nat.fib n` | `Data/Nat/Fib/Basic.lean` | divisibility transfer from indices。 |
| `Nat.fib_succ_eq_sum_choose` | `(n : ℕ) : Nat.fib (n + 1) = ∑ p ∈ Finset.antidiagonal n, p.1.choose p.2` | `Data/Nat/Fib/Basic.lean` | binomial-sum form。 |
| `Nat.fib_succ_eq_succ_sum` | `(n : ℕ) : Nat.fib (n + 1) = ∑ k ∈ Finset.range n, Nat.fib k + 1` | `Data/Nat/Fib/Basic.lean` | partial sums identity。 |

Fast computation support:

| declaration | signature | path | 用途 |
|---|---|---|---|
| `Nat.fastFib` | `(n : ℕ) : ℕ` | `Data/Nat/Fib/Basic.lean` | binary-recursive Fibonacci implementation。 |
| `Nat.fastFib_eq` | `(n : ℕ) : n.fastFib = Nat.fib n` | `Data/Nat/Fib/Basic.lean` | correctness of `fastFib`。 |
| `Nat.fib_eq_fastFib` | `Nat.fib = Nat.fastFib` | `Data/Nat/Fib/Basic.lean` | compiler simplification bridge。 |

## 3. Zeckendorf

核心文件：`Data/Nat/Fib/Zeckendorf.lean`

mathlib 的 Zeckendorf API 使用“Fibonacci index list”作为 representation；没有单独的
`Nat.Zeckendorf` declaration。合法 representation predicate 是 `List.IsZeckendorfRep`，数值
decode 是 `(l.map Nat.fib).sum`。

| declaration | signature | path | 用途 |
|---|---|---|---|
| `List.IsZeckendorfRep` | `(l : List ℕ) : Prop` | `Data/Nat/Fib/Zeckendorf.lean` | Predicate for a list of Fibonacci indices: `l ++ [0]` is chained by `fun a b ↦ b + 2 ≤ a`; read left-to-right, indices drop by at least `2`, and all used indices are at least `2`。 |
| `List.IsZeckendorfRep_nil` | `[].IsZeckendorfRep` | `Data/Nat/Fib/Zeckendorf.lean` | empty representation is valid。 |
| `List.IsZeckendorfRep.sum_fib_lt` | `{n : ℕ} {l : List ℕ} : l.IsZeckendorfRep → (∀ a ∈ (l ++ [0]).head?, a < n) → (List.map Nat.fib l).sum < Nat.fib n` | `Data/Nat/Fib/Zeckendorf.lean` | bounding lemma used by uniqueness/greedy proof。 |
| `Nat.greatestFib` | `(n : ℕ) : ℕ` | `Data/Nat/Fib/Zeckendorf.lean` | greedy step: greatest index whose Fibonacci value is `≤ n`。 |
| `Nat.fib_greatestFib_le` | `(n : ℕ) : Nat.fib n.greatestFib ≤ n` | `Data/Nat/Fib/Zeckendorf.lean` | selected Fibonacci value is admissible。 |
| `Nat.greatestFib_mono` | `Monotone Nat.greatestFib` | `Data/Nat/Fib/Zeckendorf.lean` | monotonicity of greedy index。 |
| `Nat.le_greatestFib` | `{m n : ℕ} : m ≤ n.greatestFib ↔ Nat.fib m ≤ n` | `Data/Nat/Fib/Zeckendorf.lean` | characterize `greatestFib` by a Galois-style inequality。 |
| `Nat.greatestFib_lt` | `{m n : ℕ} : m.greatestFib < n ↔ m < Nat.fib n` | `Data/Nat/Fib/Zeckendorf.lean` | dual comparison lemma。 |
| `Nat.lt_fib_greatestFib_add_one` | `(n : ℕ) : n < Nat.fib (n.greatestFib + 1)` | `Data/Nat/Fib/Zeckendorf.lean` | greedy index is maximal。 |
| `Nat.greatestFib_fib` | `{n : ℕ} : n ≠ 1 → (Nat.fib n).greatestFib = n` | `Data/Nat/Fib/Zeckendorf.lean` | inverse behavior on Fibonacci numbers, excluding the `F₁ = F₂` ambiguity。 |
| `Nat.greatestFib_eq_zero` | `{n : ℕ} : n.greatestFib = 0 ↔ n = 0` | `Data/Nat/Fib/Zeckendorf.lean` | zero characterization。 |
| `Nat.greatestFib_pos` | `{n : ℕ} : 0 < n.greatestFib ↔ 0 < n` | `Data/Nat/Fib/Zeckendorf.lean` | positivity bridge。 |
| `Nat.greatestFib_sub_fib_greatestFib_le_greatestFib` | `{n : ℕ} (hn : n ≠ 0) : (n - Nat.fib n.greatestFib).greatestFib ≤ n.greatestFib - 2` | `Data/Nat/Fib/Zeckendorf.lean` | proves greedy recursion keeps non-adjacent indices。 |
| `Nat.zeckendorf` | `ℕ → List ℕ` | `Data/Nat/Fib/Zeckendorf.lean` | greedy Zeckendorf representation function。 |
| `Nat.zeckendorf_zero` | `Nat.zeckendorf 0 = []` | `Data/Nat/Fib/Zeckendorf.lean` | zero equation for greedy representation。 |
| `Nat.zeckendorf_succ` | `(n : ℕ) : (n + 1).zeckendorf = (n + 1).greatestFib :: (n + 1 - Nat.fib (n + 1).greatestFib).zeckendorf` | `Data/Nat/Fib/Zeckendorf.lean` | recursive equation for positive inputs。 |
| `Nat.zeckendorf_of_pos` | `{n : ℕ} : 0 < n → n.zeckendorf = n.greatestFib :: (n - Nat.fib n.greatestFib).zeckendorf` | `Data/Nat/Fib/Zeckendorf.lean` | positive-case unfolding lemma。 |
| `Nat.isZeckendorfRep_zeckendorf` | `(n : ℕ) : n.zeckendorf.IsZeckendorfRep` | `Data/Nat/Fib/Zeckendorf.lean` | greedy output is a valid Zeckendorf representation。 |
| `Nat.zeckendorf_sum_fib` | `{l : List ℕ} : l.IsZeckendorfRep → (List.map Nat.fib l).sum.zeckendorf = l` | `Data/Nat/Fib/Zeckendorf.lean` | uniqueness: a valid representation round-trips through greedy normalization。 |
| `Nat.sum_zeckendorf_fib` | `(n : ℕ) : (List.map Nat.fib n.zeckendorf).sum = n` | `Data/Nat/Fib/Zeckendorf.lean` | existence: greedy representation decodes to the input。 |
| `Nat.zeckendorfEquiv` | `ℕ ≃ { l // l.IsZeckendorfRep }` | `Data/Nat/Fib/Zeckendorf.lean` | Zeckendorf theorem as an equivalence between naturals and valid representations。 |

Use for document theorem 5.3: `Nat.zeckendorfEquiv`, with `Nat.sum_zeckendorf_fib` for existence and
`Nat.zeckendorf_sum_fib` for uniqueness. Use for theorem 5.5: build the PZG-side carrier and map it to
the subtype `{l // l.IsZeckendorfRep}`; mathlib already supplies the natural-number side of the bijection.

## 4. Prime factorization and unique factorization

核心文件：`Data/Nat/Factorization/Defs.lean`, `Data/Nat/Factorization/Basic.lean`,
`Data/Nat/Factors.lean`, `RingTheory/UniqueFactorizationDomain/*.lean`

### Natural-number factorization by exponent vector

| declaration | signature | path | 用途 |
|---|---|---|---|
| `Nat.factorization` | `(n : ℕ) : ℕ →₀ ℕ` | `Data/Nat/Factorization/Defs.lean` | finite-support map `p ↦ v_p(n)`。 |
| `Nat.support_factorization` | `(n : ℕ) : n.factorization.support = n.primeFactors` | `Data/Nat/Factorization/Defs.lean` | support is exactly the prime factor finset。 |
| `Nat.factorization_def` | `(n : ℕ) {p : ℕ} (pp : Nat.Prime p) : n.factorization p = padicValNat p n` | `Data/Nat/Factorization/Defs.lean` | connects factorization coordinates to `padicValNat`。 |
| `Nat.primeFactorsList_count_eq` | `{n p : ℕ} : List.count p n.primeFactorsList = n.factorization p` | `Data/Nat/Factorization/Defs.lean` | bridge between list multiplicity and exponent vector。 |
| `Nat.factorization_eq_primeFactorsList_multiset` | `(n : ℕ) : n.factorization = Multiset.toFinsupp ↑n.primeFactorsList` | `Data/Nat/Factorization/Defs.lean` | converts prime factor list to finsupp representation。 |
| `Nat.factorization_prod_pow_eq_self` | `{n : ℕ} (hn : n ≠ 0) : (n.factorization.prod fun p e => p ^ e) = n` | `Data/Nat/Factorization/Defs.lean` | reconstructs a nonzero natural from its exponent vector。 |
| `Nat.eq_of_factorization_eq` | `{a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : ∀ p, a.factorization p = b.factorization p) : a = b` | `Data/Nat/Factorization/Defs.lean` | uniqueness from coordinatewise exponent equality。 |
| `Nat.eq_of_factorization_eq'` | `{a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a.factorization = b.factorization) : a = b` | `Data/Nat/Factorization/Defs.lean` | uniqueness from finsupp equality。 |
| `Nat.factorization_inj` | `Set.InjOn Nat.factorization {x | x ≠ 0}` | `Data/Nat/Factorization/Defs.lean` | injectivity of factorization on nonzero naturals。 |
| `Nat.factorization_zero` | `Nat.factorization 0 = 0` | `Data/Nat/Factorization/Defs.lean` | zero edge case。 |
| `Nat.factorization_one` | `Nat.factorization 1 = 0` | `Data/Nat/Factorization/Defs.lean` | unit edge case。 |
| `Nat.factorization_eq_zero_iff` | `(n p : ℕ) : n.factorization p = 0 ↔ ¬Nat.Prime p ∨ ¬p ∣ n ∨ n = 0` | `Data/Nat/Factorization/Defs.lean` | coordinate-zero characterization。 |
| `Nat.factorization_eq_zero_of_not_prime` | `(n : ℕ) {p : ℕ} (hp : ¬Nat.Prime p) : n.factorization p = 0` | `Data/Nat/Factorization/Defs.lean` | non-prime coordinates vanish。 |
| `Nat.factorization_eq_zero_of_not_dvd` | `{n p : ℕ} (h : ¬p ∣ n) : n.factorization p = 0` | `Data/Nat/Factorization/Defs.lean` | non-divisor coordinates vanish。 |
| `Nat.factorization_mul` | `{a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : (a * b).factorization = a.factorization + b.factorization` | `Data/Nat/Factorization/Defs.lean` | theorem 4.4 `v_p(ab)=v_p(a)+v_p(b)` at finsupp level。 |
| `Nat.factorization_prod` | `{α : Type u} {S : Finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) : (S.prod g).factorization = ∑ x ∈ S, (g x).factorization` | `Data/Nat/Factorization/Defs.lean` | product-level additive exponent formula。 |
| `Nat.factorization_prod_apply` | `{α : Type u} {p : ℕ} {S : Finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) : (S.prod g).factorization p = ∑ x ∈ S, (g x).factorization p` | `Data/Nat/Factorization/Basic.lean` | product formula at one prime coordinate。 |
| `Nat.factorization_pow` | `(n k : ℕ) : (n ^ k).factorization = k • n.factorization` | `Data/Nat/Factorization/Defs.lean` | power-level exponent formula。 |
| `Nat.Prime.factorization` | `{p : ℕ} (hp : Nat.Prime p) : p.factorization = Finsupp.single p 1` | `Data/Nat/Factorization/Defs.lean` | factorization of a prime。 |
| `Nat.Prime.factorization_pow` | `{p k : ℕ} (hp : Nat.Prime p) : (p ^ k).factorization = Finsupp.single p k` | `Data/Nat/Factorization/Defs.lean` | factorization of a prime power。 |
| `Nat.Prime.factorization_self` | `{p : ℕ} (hp : Nat.Prime p) : p.factorization p = 1` | `Data/Nat/Factorization/Basic.lean` | coordinate value for a prime itself。 |
| `Nat.factorization_pow_self` | `{p n : ℕ} (hp : Nat.Prime p) : (p ^ n).factorization p = n` | `Data/Nat/Factorization/Basic.lean` | coordinate value for a prime power。 |
| `Nat.factorization_le_iff_dvd` | `{d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) : d.factorization ≤ n.factorization ↔ d ∣ n` | `Data/Nat/Factorization/Defs.lean` | divisibility as coordinatewise exponent inequality。 |
| `Nat.Prime.pow_dvd_iff_le_factorization` | `{p k n : ℕ} (pp : Nat.Prime p) (hn : n ≠ 0) : p ^ k ∣ n ↔ k ≤ n.factorization p` | `Data/Nat/Factorization/Basic.lean` | prime-power divisibility criterion。 |
| `Nat.Prime.dvd_iff_one_le_factorization` | `{p n : ℕ} (pp : Nat.Prime p) (hn : n ≠ 0) : p ∣ n ↔ 1 ≤ n.factorization p` | `Data/Nat/Factorization/Basic.lean` | prime divisibility criterion。 |
| `Nat.prod_pow_factorization_eq_self` | `{f : ℕ →₀ ℕ} (hf : ∀ p ∈ f.support, Nat.Prime p) : (f.prod fun p e => p ^ e).factorization = f` | `Data/Nat/Factorization/Defs.lean` | any prime-supported finsupp reconstructs and refactorizes to itself。 |
| `Nat.eq_factorization_iff` | `{n : ℕ} {f : ℕ →₀ ℕ} (hn : n ≠ 0) (hf : ∀ p ∈ f.support, Nat.Prime p) : f = n.factorization ↔ (f.prod fun p e => p ^ e) = n` | `Data/Nat/Factorization/Basic.lean` | exact iff between exponent vector and reconstructed natural。 |
| `Nat.factorizationEquiv` | `ℕ+ ≃ { f : ℕ →₀ ℕ // ∀ p ∈ f.support, Nat.Prime p }` | `Data/Nat/Factorization/Defs.lean` | equivalence between positive naturals and prime-supported exponent vectors。 |
| `Nat.factorizationEquiv_inv_apply` | `{f : ℕ →₀ ℕ} (hf : ∀ p ∈ f.support, Nat.Prime p) : ↑(Nat.factorizationEquiv.symm ⟨f, hf⟩) = f.prod fun p e => p ^ e` | `Data/Nat/Factorization/Basic.lean` | inverse map computes as product of prime powers。 |

### Natural-number factorization by prime list

| declaration | signature | path | 用途 |
|---|---|---|---|
| `Nat.primeFactorsList` | `ℕ → List ℕ` | `Data/Nat/Factors.lean` | sorted prime factorization list。 |
| `Nat.prod_primeFactorsList` | `{n : ℕ} : n ≠ 0 → n.primeFactorsList.prod = n` | `Data/Nat/Factors.lean` | reconstructs a nonzero natural from its factor list。 |
| `Nat.prime_of_mem_primeFactorsList` | `{n p : ℕ} : p ∈ n.primeFactorsList → Nat.Prime p` | `Data/Nat/Factors.lean` | entries are prime。 |
| `Nat.mem_primeFactorsList_iff_dvd` | `{n p : ℕ} (hn : n ≠ 0) (hp : Nat.Prime p) : p ∈ n.primeFactorsList ↔ p ∣ n` | `Data/Nat/Factors.lean` | membership/divisibility bridge。 |
| `Nat.primeFactorsList_prime` | `{p : ℕ} (hp : Nat.Prime p) : p.primeFactorsList = [p]` | `Data/Nat/Factors.lean` | factor list of a prime。 |
| `Nat.primeFactorsList_unique` | `{n : ℕ} {l : List ℕ} (h₁ : l.prod = n) (h₂ : ∀ p ∈ l, Nat.Prime p) : l ~ n.primeFactorsList` | `Data/Nat/Factors.lean` | uniqueness of prime factorization as list permutation。 |
| `Nat.perm_primeFactorsList_mul` | `{a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : (a * b).primeFactorsList.Perm (a.primeFactorsList ++ b.primeFactorsList)` | `Data/Nat/Factors.lean` | factor list of a nonzero product。 |
| `Nat.perm_primeFactorsList_mul_of_coprime` | `{a b : ℕ} (hab : a.Coprime b) : (a * b).primeFactorsList.Perm (a.primeFactorsList ++ b.primeFactorsList)` | `Data/Nat/Factors.lean` | product factor list under coprimality。 |

### General unique factorization monoid API

| declaration | signature | path | 用途 |
|---|---|---|---|
| `UniqueFactorizationMonoid` | `(α : Type*) [CommMonoidWithZero α] : Prop` extending `IsCancelMulZero α`, `IsWellFounded α DvdNotUnit`, with `Irreducible a ↔ Prime a` | `RingTheory/UniqueFactorizationDomain/Defs.lean` | general UFM interface if PZG later abstracts away from `ℕ`。 |
| `UniqueFactorizationMonoid.exists_prime_factors` | `[CommMonoidWithZero α] [UniqueFactorizationMonoid α] (a : α) : a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a` | `RingTheory/UniqueFactorizationDomain/Defs.lean` | existence of prime multiset factorization in any UFM。 |
| `UniqueFactorizationMonoid.factors` | `[CommMonoidWithZero α] [UniqueFactorizationMonoid α] (a : α) : Multiset α` | `RingTheory/UniqueFactorizationDomain/Defs.lean` | chosen prime factor multiset。 |
| `UniqueFactorizationMonoid.factors_prod` | `{a : α} (ane0 : a ≠ 0) : Associated (factors a).prod a` | `RingTheory/UniqueFactorizationDomain/Defs.lean` | chosen factors reconstruct up to associates。 |
| `UniqueFactorizationMonoid.factors_unique` | `{f g : Multiset α} (hf : ∀ x ∈ f, Irreducible x) (hg : ∀ x ∈ g, Irreducible x) (h : f.prod ~ᵤ g.prod) : Multiset.Rel Associated f g` | `RingTheory/UniqueFactorizationDomain/Basic.lean` | uniqueness up to associates。 |
| `Nat.instUniqueFactorizationMonoid` | `UniqueFactorizationMonoid ℕ` | `RingTheory/UniqueFactorizationDomain/Nat.lean` | natural numbers instantiate the general UFM interface。 |
| `Nat.factors_eq` | `(n : ℕ) : normalizedFactors n = n.primeFactorsList` | `RingTheory/UniqueFactorizationDomain/Nat.lean` | connects general normalized factors to `Nat.primeFactorsList`。 |

For document theorem 4.2 use either `Nat.factorization` plus `Nat.factorization_prod_pow_eq_self`, or list-level
`Nat.primeFactorsList` plus `Nat.prod_primeFactorsList`. For theorem 4.3 use `Nat.factorization_inj`,
`Nat.eq_of_factorization_eq'`, or `Nat.primeFactorsList_unique`. For theorem 4.4 use
`Nat.factorization_mul`, `Nat.factorization_prod_apply`, and `Nat.factorizationEquiv`.

## 5. Abstract rewriting, confluence, Church-Rosser, Newman

核心文件：`Logic/Relation.lean`, `Order/WellFounded.lean`, `Order/WellFoundedSet.lean`

全文搜索 `Newman`, `Confluent`, `LocallyConfluent`, `ChurchRosser`, `NormalForm` shows no generic
Newman lemma / confluence structure for arbitrary abstract rewriting. There is a free-group-specific
Church-Rosser theorem, but it is tied to word reduction. The generic reusable layer is relation closure,
join, Church-Rosser sufficient condition, and well-founded induction.

### Generic relation closure API

| declaration | signature | path | 用途 |
|---|---|---|---|
| `Relation.ReflTransGen` | `{α : Sort u} (r : α → α → Prop) (a : α) : α → Prop` | `Logic/Relation.lean` | reflexive-transitive closure of a rewrite relation。 |
| `Relation.ReflTransGen.refl` | `{r : α → α → Prop} {a : α} : Relation.ReflTransGen r a a` | `Logic/Relation.lean` | zero-step rewrite。 |
| `Relation.ReflTransGen.tail` | `Relation.ReflTransGen r a b → r b c → Relation.ReflTransGen r a c` | `Logic/Relation.lean` | append one rewrite step。 |
| `Relation.ReflTransGen.single` | `(hab : r a b) : Relation.ReflTransGen r a b` | `Logic/Relation.lean` | one-step rewrite as many-step rewrite。 |
| `Relation.ReflTransGen.trans` | `(hab : Relation.ReflTransGen r a b) (hbc : Relation.ReflTransGen r b c) : Relation.ReflTransGen r a c` | `Logic/Relation.lean` | compose rewrite sequences。 |
| `Relation.ReflTransGen.cases_head` | `(h : Relation.ReflTransGen r a b) : a = b ∨ ∃ c, r a c ∧ Relation.ReflTransGen r c b` | `Logic/Relation.lean` | split a many-step rewrite at the head。 |
| `Relation.ReflTransGen.cases_tail` | `Relation.ReflTransGen r a b → b = a ∨ ∃ c, Relation.ReflTransGen r a c ∧ r c b` | `Logic/Relation.lean` | split a many-step rewrite at the tail。 |
| `Relation.TransGen` | `{α : Sort u} (r : α → α → Prop) : α → α → Prop` | `Logic/Relation.lean` | transitive closure for positive-length rewrites。 |
| `Relation.TransGen.to_reflTransGen` | `(h : Relation.TransGen r a b) : Relation.ReflTransGen r a b` | `Logic/Relation.lean` | convert positive closure to reflexive-transitive closure。 |
| `Relation.ReflGen` | `{α : Sort u} (r : α → α → Prop) (a : α) : α → Prop` | `Logic/Relation.lean` | reflexive closure。 |
| `Relation.SymmGen` | `{α : Sort u} (r : α → α → Prop) (a b : α) : Prop` | `Logic/Relation.lean` | symmetric closure。 |
| `Relation.EqvGen` | `{α : Sort u} (r : α → α → Prop) : α → α → Prop` | `Logic/Relation.lean` | equivalence closure of a relation。 |
| `Relation.Join` | `{α : Sort u} (r : α → α → Prop) : α → α → Prop` | `Logic/Relation.lean` | `Join r b c` means `b` and `c` rewrite to a common target under `r`。 |
| `Relation.church_rosser` | `(h : ∀ a b c, r a b → r a c → ∃ d, Relation.ReflGen r b d ∧ Relation.ReflTransGen r c d) (hab : Relation.ReflTransGen r a b) (hac : Relation.ReflTransGen r a c) : Relation.Join (Relation.ReflTransGen r) b c` | `Logic/Relation.lean` | lifts a strong one-step diamond condition to Church-Rosser for many-step closure。 |
| `Relation.equivalence_join_reflTransGen` | `(h : ∀ a b c, r a b → r a c → ∃ d, Relation.ReflGen r b d ∧ Relation.ReflTransGen r c d) : Equivalence (Relation.Join (Relation.ReflTransGen r))` | `Logic/Relation.lean` | equivalence of join relation under the same diamond-style condition。 |

### Well-founded base

| declaration | signature | path | 用途 |
|---|---|---|---|
| `WellFounded.induction` | `(hwf : WellFounded r) {C : α → Prop} (a : α) (h : ∀ x, (∀ y, r y x → C y) → C x) : C a` | Lean core, supplemented by `Order/WellFounded.lean` | induction principle for terminating rewrite relations。 |
| `WellFounded.mono` | `(hr : WellFounded r) (h : ∀ a b, r' a b → r a b) : WellFounded r'` | `Order/WellFounded.lean` | transport termination to a subrelation。 |
| `Set.WellFoundedOn` | `(s : Set α) (r : α → α → Prop) : Prop` | `Order/WellFoundedSet.lean` | well-foundedness restricted to a subset。 |
| `Set.WellFoundedOn.induction` | `(hs : s.WellFoundedOn r) (hx : x ∈ s) (hP : ∀ y ∈ s, (∀ z ∈ s, r z y → P z) → P y) : P x` | `Order/WellFoundedSet.lean` | subset-restricted termination induction。 |
| `Set.wellFoundedOn_univ` | `(Set.univ : Set α).WellFoundedOn r ↔ WellFounded r` | `Order/WellFoundedSet.lean` | connect subset and global well-foundedness。 |
| `WellFounded.wellFoundedOn` | `WellFounded r → s.WellFoundedOn r` | `Order/WellFoundedSet.lean` | restrict global well-foundedness to a subset。 |

### Domain-specific Church-Rosser already in mathlib

| declaration | signature | path | 用途 |
|---|---|---|---|
| `FreeGroup.Red.church_rosser` | `{α : Type u} {L₁ L₂ L₃ : List (α × Bool)} : FreeGroup.Red L₁ L₂ → FreeGroup.Red L₁ L₃ → Relation.Join FreeGroup.Red L₂ L₃` | `GroupTheory/FreeGroup/Basic.lean` | Church-Rosser for free group word reduction only。 |
| `FreeAddGroup.Red.church_rosser` | `{α : Type u} {L₁ L₂ L₃ : List (α × Bool)} : FreeAddGroup.Red L₁ L₂ → FreeAddGroup.Red L₁ L₃ → Relation.Join FreeAddGroup.Red L₂ L₃` | `GroupTheory/FreeGroup/Basic.lean` | additive free-group analogue only。 |

Conclusion for document theorem 3.2: mathlib has the relation/well-founded substrate, but no generic
`termination + local confluence => unique normal form` Newman package. The PZG abstract rewriting layer
should define its own `NormalForm`, `Confluent`, `LocallyConfluent`, and Newman lemma over
`Relation.ReflTransGen`, using `WellFounded.induction`.

## 6. Integers, traces, quadratic integer tools, floor/round/sqrt

### `ℤ√d`

核心文件：`NumberTheory/Zsqrtd/Basic.lean`, `NumberTheory/Zsqrtd/ToReal.lean`

mathlib has `Zsqrtd`, a ring `ℤ√d` with elements `a + b√d`. It is not literally `ℤ[φ]`, because
`φ = (1 + √5) / 2`; for `φ`-arithmetic one can either work in `ℤ√5` plus parity constraints, or
introduce the order `ℤ[(1+√5)/2]` on top of the existing `Zsqrtd` infrastructure.

| declaration | signature | path | 用途 |
|---|---|---|---|
| `Zsqrtd` | `(d : ℤ) : Type` with fields `re : ℤ`, `im : ℤ` | `NumberTheory/Zsqrtd/Basic.lean` | carrier for `a + b√d`。 |
| `Zsqrtd.ofInt` | `{d : ℤ} (n : ℤ) : ℤ√d` | `NumberTheory/Zsqrtd/Basic.lean` | embed integers into `ℤ√d`。 |
| `Zsqrtd.sqrtd` | `{d : ℤ} : ℤ√d` | `NumberTheory/Zsqrtd/Basic.lean` | distinguished `√d` element。 |
| `Zsqrtd.re_mul` | `{d : ℤ} (z w : ℤ√d) : (z * w).re = z.re * w.re + d * z.im * w.im` | `NumberTheory/Zsqrtd/Basic.lean` | real component of product。 |
| `Zsqrtd.im_mul` | `{d : ℤ} (z w : ℤ√d) : (z * w).im = z.re * w.im + z.im * w.re` | `NumberTheory/Zsqrtd/Basic.lean` | `√d` component of product。 |
| `Zsqrtd.re_star` | `{d : ℤ} (z : ℤ√d) : (star z).re = z.re` | `NumberTheory/Zsqrtd/Basic.lean` | conjugation fixes the integer component。 |
| `Zsqrtd.im_star` | `{d : ℤ} (z : ℤ√d) : (star z).im = -z.im` | `NumberTheory/Zsqrtd/Basic.lean` | conjugation negates the `√d` component。 |
| `Zsqrtd.dmuld` | `{d : ℤ} : Zsqrtd.sqrtd * Zsqrtd.sqrtd = ↑d` | `NumberTheory/Zsqrtd/Basic.lean` | proves `(√d)^2 = d` in the ring。 |
| `Zsqrtd.decompose` | `{d x y : ℤ} : ({ re := x, im := y } : ℤ√d) = ↑x + Zsqrtd.sqrtd * ↑y` | `NumberTheory/Zsqrtd/Basic.lean` | canonical decomposition into integer and `√d` parts。 |
| `Zsqrtd.mul_star` | `{d x y : ℤ} : ({ re := x, im := y } : ℤ√d) * star { re := x, im := y } = ↑x * ↑x - ↑d * ↑y * ↑y` | `NumberTheory/Zsqrtd/Basic.lean` | norm as product with conjugate。 |
| `Zsqrtd.norm` | `{d : ℤ} (n : ℤ√d) : ℤ` | `NumberTheory/Zsqrtd/Basic.lean` | norm `a^2 - d b^2`。 |
| `Zsqrtd.norm_def` | `{d : ℤ} (n : ℤ√d) : n.norm = n.re * n.re - d * n.im * n.im` | `NumberTheory/Zsqrtd/Basic.lean` | unfold norm。 |
| `Zsqrtd.norm_mul` | `{d : ℤ} (n m : ℤ√d) : (n * m).norm = n.norm * m.norm` | `NumberTheory/Zsqrtd/Basic.lean` | multiplicativity of norm。 |
| `Zsqrtd.normMonoidHom` | `{d : ℤ} : ℤ√d →* ℤ` | `NumberTheory/Zsqrtd/Basic.lean` | norm as monoid hom。 |
| `Zsqrtd.norm_eq_mul_conj` | `{d : ℤ} (n : ℤ√d) : ↑n.norm = n * star n` | `NumberTheory/Zsqrtd/Basic.lean` | connects norm and conjugation。 |
| `Zsqrtd.norm_conj` | `{d : ℤ} (x : ℤ√d) : (star x).norm = x.norm` | `NumberTheory/Zsqrtd/Basic.lean` | conjugation preserves norm。 |
| `Zsqrtd.lift` | `{R : Type} [CommRing R] {d : ℤ} : { r // r * r = ↑d } ≃ (ℤ√d →+* R)` | `NumberTheory/Zsqrtd/Basic.lean` | universal property: map out of `ℤ√d` by choosing a square root of `d`。 |
| `Zsqrtd.lift_injective` | `{R : Type} [CommRing R] [CharZero R] {d : ℤ} (r : { r // r * r = ↑d }) (hd : ∀ n : ℤ, d ≠ n * n) : Function.Injective ⇑(Zsqrtd.lift r)` | `NumberTheory/Zsqrtd/Basic.lean` | injectivity of the lifted embedding under nonsquare condition。 |
| `Zsqrtd.toReal` | `{d : ℤ} (h : 0 ≤ d) : ℤ√d →+* ℝ` | `NumberTheory/Zsqrtd/ToReal.lean` | real embedding using the positive `Real.sqrt` root。 |
| `Zsqrtd.toReal_injective` | `{d : ℤ} (h0d : 0 ≤ d) (hd : ∀ n : ℤ, d ≠ n * n) : Function.Injective ⇑(Zsqrtd.toReal h0d)` | `NumberTheory/Zsqrtd/ToReal.lean` | injectivity of the real embedding for nonsquare `d`。 |

Use for theorem 6.22: `star`, `norm`, and `toReal` can express Galois conjugation and trace/norm-style
integer arguments. The half-integer nature of `φ` is the part not directly represented by `Zsqrtd`.

### Square root, floor, and round

| declaration | signature | path | 用途 |
|---|---|---|---|
| `Nat.sqrt` | `(n : ℕ) : ℕ` | `Data/Nat/Sqrt.lean` | integer square root on naturals; `Nat.sqrt 5 = 2` is computable by simplification。 |
| `Nat.sqrt_le` | `(n : ℕ) : n.sqrt * n.sqrt ≤ n` | `Data/Nat/Sqrt.lean` | lower square bound。 |
| `Nat.le_sqrt` | `{m n : ℕ} : m ≤ n.sqrt ↔ m * m ≤ n` | `Data/Nat/Sqrt.lean` | characterize `Nat.sqrt` by square inequality。 |
| `Nat.sqrt_lt` | `{m n : ℕ} : m.sqrt < n ↔ m < n * n` | `Data/Nat/Sqrt.lean` | upper square bound as strict inequality。 |
| `Nat.eq_sqrt` | `{n a : ℕ} : a = n.sqrt ↔ a * a ≤ n ∧ n < (a + 1) * (a + 1)` | `Data/Nat/Sqrt.lean` | exact characterization of square root value。 |
| `Nat.sqrt_eq` | `(n : ℕ) : (n * n).sqrt = n` | `Data/Nat/Sqrt.lean` | square root of a perfect square。 |
| `Nat.exists_mul_self` | `(x : ℕ) : (∃ n, n * n = x) ↔ x.sqrt * x.sqrt = x` | `Data/Nat/Sqrt.lean` | perfect-square test。 |
| `Int.sqrt` | `(z : ℤ) : ℤ` | `Data/Int/Sqrt.lean` | integer square root via `Nat.sqrt (Int.toNat z)`。 |
| `Int.sqrt_eq` | `(n : ℤ) : Int.sqrt (n * n) = ↑n.natAbs` | `Data/Int/Sqrt.lean` | integer square root of square。 |
| `Int.exists_mul_self` | `(x : ℤ) : (∃ n, n * n = x) ↔ Int.sqrt x * Int.sqrt x = x` | `Data/Int/Sqrt.lean` | integer perfect-square test。 |
| `Int.floor` | `{α : Type u} [Ring α] [LinearOrder α] [FloorRing α] : α → ℤ` | `Algebra/Order/Floor/Defs.lean` | integer-valued floor。 |
| `Int.ceil` | `{α : Type u} [Ring α] [LinearOrder α] [FloorRing α] : α → ℤ` | `Algebra/Order/Floor/Defs.lean` | integer-valued ceiling。 |
| `Int.fract` | `{α : Type u} [Ring α] [LinearOrder α] [FloorRing α] (a : α) : α` | `Algebra/Order/Floor/Defs.lean` | fractional part `a - floor a`。 |
| `Int.le_floor` | `{z : ℤ} {a : α} : z ≤ ⌊a⌋ ↔ ↑z ≤ a` | `Algebra/Order/Floor/Defs.lean` | floor lower-adjoint characterization。 |
| `Int.floor_lt` | `{z : ℤ} {a : α} : ⌊a⌋ < z ↔ a < ↑z` | `Algebra/Order/Floor/Defs.lean` | upper characterization of floor。 |
| `Int.floor_le` | `(a : α) : ↑⌊a⌋ ≤ a` | `Algebra/Order/Floor/Defs.lean` | floor is below input。 |
| `Int.ceil_le` | `{z : ℤ} {a : α} : ⌈a⌉ ≤ z ↔ a ≤ ↑z` | `Algebra/Order/Floor/Defs.lean` | ceil upper-adjoint characterization。 |
| `Int.lt_ceil` | `{z : ℤ} {a : α} : z < ⌈a⌉ ↔ ↑z < a` | `Algebra/Order/Floor/Defs.lean` | lower characterization of ceil。 |
| `Int.le_ceil` | `(a : α) : a ≤ ↑⌈a⌉` | `Algebra/Order/Floor/Defs.lean` | ceil is above input。 |
| `round` | `{α : Type u} [Ring α] [LinearOrder α] [FloorRing α] (x : α) : ℤ` | `Algebra/Order/Round.lean` | nearest integer, ties toward positive infinity。 |
| `round_eq_div` | `(x : α) : round x = (⌊2 * x⌋ + 1) / 2` under ordered-ring assumptions | `Algebra/Order/Round.lean` | formula for `round` via floor。 |
| `round_eq` | `(x : α) : round x = ⌊x + 1 / 2⌋` under ordered-field assumptions | `Algebra/Order/Round.lean` | simpler rounding formula for fields。 |
| `round_eq_iff` | `{x : α} {n : ℤ} : round x = n ↔ x ∈ Set.Ico (↑n - 1 / 2) (↑n + 1 / 2)` | `Algebra/Order/Round.lean` | exact interval characterization of rounding。 |
| `abs_sub_round` | `(x : α) : |x - ↑(round x)| ≤ 1 / 2` | `Algebra/Order/Round.lean` | nearest-integer error bound。 |
| `round_le` | `(x : α) (z : ℤ) : |x - ↑(round x)| ≤ |x - ↑z|` | `Algebra/Order/Round.lean` | optimality of `round` among integers。 |

## Formalization feasibility ratings

| document theorem | rating | mathlib route |
|---|---|---|
| 4.2 decomposition existence | `mathlib-direct` | Use `Nat.primeFactorsList` / `Nat.prod_primeFactorsList`, or `Nat.factorization` / `Nat.factorization_prod_pow_eq_self`; for positive naturals, `Nat.factorizationEquiv` packages the equivalence. |
| 4.3 decomposition uniqueness | `mathlib-direct` | Use `Nat.primeFactorsList_unique`, `Nat.eq_of_factorization_eq'`, or `Nat.factorization_inj`. |
| 4.4 freeness and additivity | `mathlib-direct` | Use `Nat.factorizationEquiv` for prime-supported exponent vectors and `Nat.factorization_mul` / `Nat.factorization_prod_apply` for additivity. |
| 5.3 Zeckendorf uniqueness | `mathlib-direct` | `Nat.zeckendorfEquiv` is exactly existence plus uniqueness for valid non-adjacent Fibonacci-index lists. |
| 5.5 PZG bijection | `mathlib-assisted` | mathlib gives `Nat.factorizationEquiv` and `Nat.zeckendorfEquiv`; PZG needs a custom carrier and a bridge between its syntax and these subtypes. |
| 5.6 normalization equals multiplication | `mathlib-assisted` | factorization additivity and reconstruction are direct, but the PZG normalization relation/function must be defined and connected to them. |
| 6.3 double-sided lift | `mathlib-assisted` | `Real.coe_fib_eq`, `Real.coe_intFib_eq`, and the `φ`/`ψ` identities are direct; the document-specific lift interface still needs assembly. |
| 6.22 deficit is an integer | `mathlib-assisted` | `Zsqrtd.star`, `Zsqrtd.norm`, and `Zsqrtd.toReal` support conjugation/integrality arguments, but `ℤ[φ]` is not directly a `Zsqrtd` carrier because of the factor `1/2`. |
| 6.25 deficit three-value theorem | `mathlib-assisted` | Binet, `round`, floor bounds, and `Zsqrtd` give the arithmetic substrate; the actual trichotomy is document-specific and must be proved over the chosen deficit definition. |

