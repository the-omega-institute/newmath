import BEDC.Derived.DeRhamUp

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Hist

theorem DeRhamDoubleExteriorPacket_root_carrier_obligation
    {d : BHist -> BHist} {omega eta theta zero : BHist} :
    DeRhamDoubleExteriorPacket d omega eta theta zero ->
      DeRhamBoundary d eta ∧ DeRhamBoundary d theta ∧ hsame theta zero ∧
        hsame (d eta) BHist.Empty ∧ hsame zero BHist.Empty := by
  intro packet
  have boundaryRows := DeRhamDoubleExteriorPacket_boundary packet
  have etaBoundary : DeRhamBoundary d eta :=
    Exists.intro omega packet.left
  exact And.intro etaBoundary
    (And.intro boundaryRows.right.left
      (And.intro boundaryRows.left
        (And.intro boundaryRows.right.right packet.right.right.right.right)))

end BEDC.Derived.DeRhamUp
