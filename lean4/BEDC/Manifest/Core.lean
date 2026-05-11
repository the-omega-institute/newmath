namespace BEDC.Manifest

/-- 单条 paper claim 在 Lean 内部的登记: paper 标签 + Lean 全限定名 + 命题本身 + 证明项。
    依赖字段 `proof : prop` 让 Lean 在 elaborate manifest 时强制 (prop, proof) 类型一致;
    manifest 的"wellformedness"等同于 Lean kernel 对这个 list 的 type-check。-/
structure ClaimEntry where
  paper_label : String
  lean_name : String
  prop : Prop
  proof : prop

end BEDC.Manifest
