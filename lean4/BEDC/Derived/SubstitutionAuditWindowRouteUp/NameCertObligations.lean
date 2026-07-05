import BEDC.Derived.SubstitutionAuditWindowRouteUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubstitutionAuditWindowRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubstitutionAuditWindowRoute_namecert_obligations
    [AskSetup] [PackageSetup]
    {T D L M C G B H R P N td dl lm mc cg gb bh hr : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory D ->
        UnaryHistory L ->
          UnaryHistory M ->
            UnaryHistory C ->
              UnaryHistory G ->
                UnaryHistory B ->
                  UnaryHistory H ->
                    UnaryHistory R ->
                      Cont T D td ->
                        Cont td L dl ->
                          Cont dl M lm ->
                            Cont lm C mc ->
                              Cont mc G cg ->
                                Cont cg B gb ->
                                  Cont gb H bh ->
                                    Cont bh R hr ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle N pkg ->
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row B ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row T ∨ hsame row D ∨
                                                  hsame row L ∨ hsame row M ∨
                                                    hsame row C ∨ hsame row G ∨
                                                      hsame row B)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont T D td ∧
                                                  Cont td L dl ∧ Cont dl M lm ∧
                                                    Cont lm C mc ∧ Cont mc G cg ∧
                                                      Cont cg B gb ∧
                                                        PkgSig bundle P pkg)
                                              hsame ∧
                                            UnaryHistory td ∧ UnaryHistory dl ∧
                                              UnaryHistory lm ∧ UnaryHistory mc ∧
                                                UnaryHistory cg ∧ UnaryHistory gb ∧
                                                  hsame gb (append cg B) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro unaryT unaryD unaryL unaryM unaryC unaryG unaryB _unaryH _unaryR
    termWindow windowShift shiftSubst substComposition compositionGenerator
    generatorHandoff handoffTransport transportRoute provenancePkg _namePkg
  have unaryTd : UnaryHistory td :=
    unary_cont_closed unaryT unaryD termWindow
  have unaryDl : UnaryHistory dl :=
    unary_cont_closed unaryTd unaryL windowShift
  have unaryLm : UnaryHistory lm :=
    unary_cont_closed unaryDl unaryM shiftSubst
  have unaryMc : UnaryHistory mc :=
    unary_cont_closed unaryLm unaryC substComposition
  have unaryCg : UnaryHistory cg :=
    unary_cont_closed unaryMc unaryG compositionGenerator
  have unaryGb : UnaryHistory gb :=
    unary_cont_closed unaryCg unaryB generatorHandoff
  have gbReadback : hsame gb (append cg B) :=
    generatorHandoff
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro B ⟨hsame_refl B, unaryB⟩
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
                    (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, termWindow, windowShift, shiftSubst, substComposition,
            compositionGenerator, generatorHandoff, provenancePkg⟩
    }
  · exact
      ⟨unaryTd, unaryDl, unaryLm, unaryMc, unaryCg, unaryGb, gbReadback⟩

end BEDC.Derived.SubstitutionAuditWindowRouteUp
