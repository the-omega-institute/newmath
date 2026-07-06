import BEDC.Derived.AuditMapTemplatePacketUp.TasteGate

namespace BEDC.Derived.AuditMapTemplatePacketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditMapTemplatePacketUp_StdBridge [AskSetup] [PackageSetup]
    {U P C O F S H R K N posRead condRead obsRead frontRead siblingRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditMapTemplatePacketCarrier U P C O F S H R K N bundle pkg ->
      Cont P C posRead ->
        Cont C O condRead ->
          Cont O F obsRead ->
            Cont F S frontRead ->
              Cont S H siblingRead ->
                Cont R K nameRead ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                      (fun row : BHist => hsame row N ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row U ∨ hsame row P ∨ hsame row C ∨ hsame row O ∨
                          hsame row F ∨ hsame row S ∨ hsame row H ∨ hsame row R ∨
                            hsame row K ∨ hsame row N)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle N pkg ∧ Cont R K nameRead)
                      hsame ∧
                      UnaryHistory posRead ∧ UnaryHistory condRead ∧
                        UnaryHistory obsRead ∧ UnaryHistory frontRead ∧
                          UnaryHistory siblingRead ∧ Cont C O F := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier posRoute condRoute obsRoute frontRoute siblingRoute nameRoute namePkg
  obtain ⟨_unaryU, unaryP, unaryC, unaryO, unaryF, unaryS, unaryH, _unaryR, _unaryK,
    unaryN, conditionalObstructionFrontier, _provenancePkg, _carrierNamePkg⟩ := carrier
  have posUnary : UnaryHistory posRead := unary_cont_closed unaryP unaryC posRoute
  have condUnary : UnaryHistory condRead := unary_cont_closed unaryC unaryO condRoute
  have obsUnary : UnaryHistory obsRead := unary_cont_closed unaryO unaryF obsRoute
  have frontUnary : UnaryHistory frontRead := unary_cont_closed unaryF unaryS frontRoute
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed unaryS unaryH siblingRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row U ∨ hsame row P ∨ hsame row C ∨ hsame row O ∨ hsame row F ∨
            hsame row S ∨ hsame row H ∨ hsame row R ∨ hsame row K ∨ hsame row N)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle N pkg ∧ Cont R K nameRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namePkg, nameRoute⟩
  }
  exact
    ⟨cert, posUnary, condUnary, obsUnary, frontUnary, siblingUnary,
      conditionalObstructionFrontier⟩

end BEDC.Derived.AuditMapTemplatePacketUp
