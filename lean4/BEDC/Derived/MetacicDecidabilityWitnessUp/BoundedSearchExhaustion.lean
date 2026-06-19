import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessBoundedSearchExhaustion [AskSetup] [PackageSetup]
    {typing sameTerm bounded finished refusal transport route provenance localName
      boundedFinished normalRead exhaustedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory typing →
      UnaryHistory sameTerm →
        UnaryHistory bounded →
          UnaryHistory finished →
            UnaryHistory refusal →
              UnaryHistory route →
                Cont typing sameTerm boundedFinished →
                  Cont bounded finished normalRead →
                    Cont normalRead refusal transport →
                      Cont transport route exhaustedRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist =>
                                  (hsame row boundedFinished ∨ hsame row normalRead ∨
                                    hsame row transport ∨ hsame row exhaustedRead) ∧
                                    UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row typing ∨ hsame row sameTerm ∨
                                    hsame row bounded ∨ hsame row finished ∨
                                      hsame row refusal ∨ hsame row transport ∨
                                        hsame row route ∨ hsame row boundedFinished ∨
                                          hsame row normalRead ∨ hsame row exhaustedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont typing sameTerm boundedFinished ∧
                                    Cont bounded finished normalRead ∧
                                      Cont normalRead refusal transport ∧
                                        Cont transport route exhaustedRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory boundedFinished ∧ UnaryHistory normalRead ∧
                                UnaryHistory transport ∧ UnaryHistory exhaustedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro typingUnary sameTermUnary boundedUnary finishedUnary refusalUnary routeUnary
    typingSameTerm boundedFinishedNormal normalRefusal transportRoute provenancePkg
    localNamePkg
  have boundedFinishedUnary : UnaryHistory boundedFinished :=
    unary_cont_closed typingUnary sameTermUnary typingSameTerm
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed boundedUnary finishedUnary boundedFinishedNormal
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed normalReadUnary refusalUnary normalRefusal
  have exhaustedReadUnary : UnaryHistory exhaustedRead :=
    unary_cont_closed transportUnary routeUnary transportRoute
  have sourceExhausted :
      (fun row : BHist =>
        (hsame row boundedFinished ∨ hsame row normalRead ∨ hsame row transport ∨
          hsame row exhaustedRead) ∧ UnaryHistory row) exhaustedRead := by
    exact ⟨Or.inr (Or.inr (Or.inr (hsame_refl exhaustedRead))), exhaustedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row boundedFinished ∨ hsame row normalRead ∨ hsame row transport ∨
              hsame row exhaustedRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typing ∨ hsame row sameTerm ∨ hsame row bounded ∨
              hsame row finished ∨ hsame row refusal ∨ hsame row transport ∨
                hsame row route ∨ hsame row boundedFinished ∨ hsame row normalRead ∨
                  hsame row exhaustedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont typing sameTerm boundedFinished ∧
              Cont bounded finished normalRead ∧ Cont normalRead refusal transport ∧
                Cont transport route exhaustedRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exhaustedRead sourceExhausted
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
        cases source.left with
        | inl sameBoundedFinished =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameBoundedFinished),
                unary_transport source.right sameRows⟩
        | inr rest =>
            cases rest with
            | inl sameNormal =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNormal)),
                    unary_transport source.right sameRows⟩
            | inr restTail =>
                cases restTail with
                | inl sameTransport =>
                    exact
                      ⟨Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows)
                            sameTransport))),
                        unary_transport source.right sameRows⟩
                | inr sameExhausted =>
                    exact
                      ⟨Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) sameExhausted))),
                        unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameBoundedFinished =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl sameBoundedFinished)))))))
      | inr rest =>
          cases rest with
          | inl sameNormal =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inl sameNormal))))))))
          | inr restTail =>
              cases restTail with
              | inl sameTransport =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inl sameTransport)))))
              | inr sameExhausted =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr (Or.inr sameExhausted))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, typingSameTerm, boundedFinishedNormal, normalRefusal,
          transportRoute, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, boundedFinishedUnary, normalReadUnary, transportUnary, exhaustedReadUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
