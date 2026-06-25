import BEDC.Derived.AnalogyCertificateGateUp.NameCertObligations

namespace BEDC.Derived.AnalogyCertificateGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AnalogyCertificateGateObligationRowScope [AskSetup] [PackageSetup]
    {S K G R V U L E F H C P N exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalogyCertificateGateCarrier S K G R V U L E F H C P N bundle pkg →
      Cont V U L →
        Cont L E exportRead →
          PkgSig bundle exportRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row V ∨ hsame row U ∨ hsame row L ∨ hsame row E ∨
                    hsame row F ∨ hsame row exportRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont V U L ∧ Cont L E exportRead ∧
                    PkgSig bundle exportRead pkg)
                hsame ∧
              UnaryHistory exportRead ∧
                PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier routeLedger routeExport exportPkg
  have vUnary : UnaryHistory V := carrier.right.right.right.right.left
  have uUnary : UnaryHistory U := carrier.right.right.right.right.right.left
  have lUnary : UnaryHistory L := carrier.right.right.right.right.right.right.left
  have eUnary : UnaryHistory E := carrier.right.right.right.right.right.right.right.left
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed lUnary eUnary routeExport
  have provenancePkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have sourceAtExport :
      (fun row : BHist => hsame row exportRead ∧ UnaryHistory row) exportRead :=
    ⟨hsame_refl exportRead, exportUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row U ∨ hsame row L ∨ hsame row E ∨ hsame row F ∨
              hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V U L ∧ Cont L E exportRead ∧
              PkgSig bundle exportRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead sourceAtExport
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeLedger, routeExport, exportPkg⟩
  }
  exact ⟨cert, exportUnary, provenancePkg⟩

end BEDC.Derived.AnalogyCertificateGateUp
