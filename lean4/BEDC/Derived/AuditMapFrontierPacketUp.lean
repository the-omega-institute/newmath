import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMapFrontierPacketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditMapFrontierPacketCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {familyTag checked conditional obstruction frontier provenance transport route localName
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory familyTag ->
      UnaryHistory checked ->
        UnaryHistory conditional ->
          UnaryHistory obstruction ->
            UnaryHistory frontier ->
              UnaryHistory provenance ->
                UnaryHistory transport ->
                  UnaryHistory route ->
                    UnaryHistory localName ->
                      Cont checked conditional route ->
                        Cont route frontier consumerRead ->
                          PkgSig bundle provenance pkg ->
                            PkgSig bundle localName pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row localName ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row familyTag ∨ hsame row checked ∨
                                      hsame row conditional ∨ hsame row obstruction ∨
                                        hsame row frontier ∨ hsame row provenance ∨
                                          hsame row route ∨ hsame row localName)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _familyTagUnary checkedUnary conditionalUnary _obstructionUnary frontierUnary
    _provenanceUnary _transportUnary _routeUnary localNameUnary checkedRoute consumerRoute
    provenancePkg localNamePkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed checkedUnary conditionalUnary checkedRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed routeUnary frontierUnary consumerRoute
  have localNameSource :
      (fun row : BHist => hsame row localName ∧ UnaryHistory row) localName := by
    exact ⟨hsame_refl localName, localNameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row familyTag ∨ hsame row checked ∨ hsame row conditional ∨
              hsame row obstruction ∨ hsame row frontier ∨ hsame row provenance ∨
                hsame row route ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localName localNameSource
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, consumerReadUnary⟩

end BEDC.Derived.AuditMapFrontierPacketUp
