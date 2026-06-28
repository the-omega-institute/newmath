namespace BEDC.Boundary.OrientedTriadicCertificate

/-!
本文件只记录定向三元证书系统的外部边界 obligation。
这些命题行不作为 kernel-side RH 证明, 也不导入主构造的有限证书不变量。
-/

structure OrientedTriadicBoundaryObligations where
  infiniteClosureTower : Prop
  zetaRouteCompleteness : Prop
  rhCriticalLineReadback : Prop
  externalMetatheorySoundness : Prop

def obligations
    (rows : OrientedTriadicBoundaryObligations) : Prop :=
  rows.infiniteClosureTower ∧
    rows.zetaRouteCompleteness ∧
      rows.rhCriticalLineReadback ∧
        rows.externalMetatheorySoundness

end BEDC.Boundary.OrientedTriadicCertificate
