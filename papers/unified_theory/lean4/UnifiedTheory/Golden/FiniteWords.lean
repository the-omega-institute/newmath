import UnifiedTheory.Golden.Carry

/-!
# ch6 有限词递推与 Cassini 守恒(命题 6.5/6.40 的有限心)

有限层的两条承重恒等:Fibonacci 递推(有限 W 词的零阶递推)与 Cassini 守恒
`F_{n+1}² − F_n·F_{n+2} = (−1)^n`(迹映射纲领 6.35–6.36 的守恒律的有限心)。

分析层(无穷生成函数 `W(x,y)`、重整化函数方程 6.5、拟晶 zeta `Z_qc` 6.8、Euler 乘积、
解析延拓)含无穷和/解析延拓,属 O-5 前沿,**此处不定义、不冒充定理**——只呈现其有限心。
-/

namespace UnifiedTheory
namespace Golden

/-- 有限 W 词递推(命题 6.5 的零阶有限心):`F_{k+2} = F_{k+1} + F_k`。 -/
theorem finiteW_recurrence (k : ℕ) :
    (Nat.fib (k + 2) : ℤ) = Nat.fib (k + 1) + Nat.fib k := by
  have h : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
  push_cast [h]; ring

/-- **Cassini 守恒**(命题 6.40 封闭律的有限心):`F_{n+1}² − F_n·F_{n+2} = (−1)^n`。 -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n := by
  induction n with
  | zero => norm_num [Nat.fib]
  | succ k ih =>
    have e1 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    have e2 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have key : (Nat.fib (k + 2) : ℤ) ^ 2 - Nat.fib (k + 1) * Nat.fib (k + 3)
        = -((Nat.fib (k + 1) : ℤ) ^ 2 - Nat.fib k * Nat.fib (k + 2)) := by
      push_cast [e1, e2]; ring
    rw [key, ih, pow_succ]; ring

end Golden
end UnifiedTheory
