import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiracPointMassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiracPointMassCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X p E U D H C P N eventRead unitRead distributionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory X ∧ UnaryHistory p ∧ UnaryHistory E ∧ UnaryHistory U ∧
        UnaryHistory D ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
          UnaryHistory N ∧ PkgSig bundle P pkg) →
      Cont p E eventRead →
        Cont eventRead U unitRead →
          Cont unitRead D distributionRead →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row distributionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row p ∨ hsame row E ∨ hsame row U ∨
                      hsame row D ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row eventRead ∨ hsame row unitRead ∨
                          hsame row distributionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont p E eventRead ∧ Cont eventRead U unitRead ∧
                      Cont unitRead D distributionRead ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory eventRead ∧ UnaryHistory unitRead ∧
                  UnaryHistory distributionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier eventRoute unitRoute distributionRoute localNamePkg
  obtain ⟨_sourceUnary, pointUnary, eventUnary, unitLedgerUnary, distributionUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _provenancePkg⟩ :=
    carrier
  have eventReadUnary : UnaryHistory eventRead :=
    unary_cont_closed pointUnary eventUnary eventRoute
  have unitReadUnary : UnaryHistory unitRead :=
    unary_cont_closed eventReadUnary unitLedgerUnary unitRoute
  have distributionReadUnary : UnaryHistory distributionRead :=
    unary_cont_closed unitReadUnary distributionUnary distributionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row distributionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row p ∨ hsame row E ∨ hsame row U ∨ hsame row D ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row eventRead ∨ hsame row unitRead ∨ hsame row distributionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont p E eventRead ∧ Cont eventRead U unitRead ∧
              Cont unitRead D distributionRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro distributionRead
          ⟨hsame_refl distributionRead, distributionReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, eventRoute, unitRoute, distributionRoute, localNamePkg⟩
  }
  exact ⟨cert, eventReadUnary, unitReadUnary, distributionReadUnary⟩

end BEDC.Derived.DiracPointMassUp
