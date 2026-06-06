import BEDC.Derived.LawlikeSequenceUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.LawlikeSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlikeSequenceNameCertObligations [AskSetup] [PackageSetup]
    {R W O H C P N requestRead observationRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W →
      UnaryHistory R →
        UnaryHistory O →
          UnaryHistory C →
            Cont W R requestRead →
              Cont R O observationRead →
                Cont observationRead C realRead →
                  PkgSig bundle realRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row observationRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row R ∨ hsame row W ∨ hsame row O ∨ hsame row H ∨
                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                              hsame row observationRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle realRead pkg ∧
                            Cont R O observationRead)
                        hsame ∧
                      UnaryHistory requestRead ∧ UnaryHistory observationRead ∧
                        UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro unaryW unaryR unaryO unaryC requestRoute observationRoute realRoute pkgSig
  have unaryRequest : UnaryHistory requestRead :=
    unary_cont_closed unaryW unaryR requestRoute
  have unaryObservation : UnaryHistory observationRead :=
    unary_cont_closed unaryR unaryO observationRoute
  have unaryReal : UnaryHistory realRead :=
    unary_cont_closed unaryObservation unaryC realRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro observationRead ⟨hsame_refl observationRead, unaryObservation⟩
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
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, pkgSig, observationRoute⟩
    }
  · constructor
    · exact unaryRequest
    · constructor
      · exact unaryObservation
      · exact unaryReal

end BEDC.Derived.LawlikeSequenceUp
