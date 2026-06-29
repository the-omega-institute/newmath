import BEDC.Derived.HypercoverUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HypercoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HypercoverCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {J U M C S D T R P N levelRead matchingRead descentRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory J →
      UnaryHistory U →
        UnaryHistory M →
          UnaryHistory C →
            UnaryHistory S →
              UnaryHistory D →
                UnaryHistory T →
                  UnaryHistory R →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont J U levelRead →
                          Cont levelRead M matchingRead →
                            Cont C S D →
                              Cont matchingRead T R →
                                Cont R P namedRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row J ∨ hsame row U ∨ hsame row M ∨
                                              hsame row C ∨ hsame row S ∨ hsame row D ∨
                                                hsame row T ∨ hsame row R ∨
                                                  hsame row P ∨ hsame row N ∨
                                                    hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont J U levelRead ∧
                                              Cont levelRead M matchingRead ∧ Cont C S D ∧
                                                Cont matchingRead T R ∧
                                                  Cont R P namedRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory levelRead ∧
                                          UnaryHistory matchingRead ∧
                                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: HypercoverUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro jUnary uUnary mUnary cUnary sUnary _dUnary tUnary rUnary pUnary _nUnary
    levelRoute matchingRoute descentRoute replayRoute namedRoute pPkg nPkg
  have _descentReadWitness : BHist := descentRead
  have levelUnary : UnaryHistory levelRead :=
    unary_cont_closed jUnary uUnary levelRoute
  have matchingUnary : UnaryHistory matchingRead :=
    unary_cont_closed levelUnary mUnary matchingRoute
  have _descentWitness : Cont C S D := descentRoute
  have replayUnary : UnaryHistory R :=
    unary_cont_closed matchingUnary tUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary pUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row J ∨ hsame row U ∨ hsame row M ∨ hsame row C ∨ hsame row S ∨
              hsame row D ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J U levelRead ∧ Cont levelRead M matchingRead ∧
              Cont C S D ∧ Cont matchingRead T R ∧ Cont R P namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, levelRoute, matchingRoute, descentRoute, replayRoute, namedRoute,
          pPkg, nPkg⟩
  }
  exact ⟨cert, levelUnary, matchingUnary, namedUnary⟩

theorem HypercoverNameCertObligations [AskSetup] [PackageSetup]
    {J U M C S D T R P N coverRead descentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory J → UnaryHistory U → UnaryHistory M → UnaryHistory S →
      UnaryHistory T → UnaryHistory P → UnaryHistory N → Cont J U coverRead →
        Cont coverRead M C → Cont C S D → Cont D T R → Cont R P descentRead →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row descentRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row J ∨ hsame row U ∨ hsame row M ∨ hsame row C ∨
                    hsame row S ∨ hsame row D ∨ hsame row T ∨ hsame row R ∨
                      hsame row P ∨ hsame row N ∨ hsame row coverRead ∨
                        hsame row descentRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont J U coverRead ∧ Cont coverRead M C ∧
                    Cont C S D ∧ Cont D T R ∧ Cont R P descentRead ∧
                      PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory coverRead ∧ UnaryHistory C ∧ UnaryHistory D ∧
                UnaryHistory R ∧ UnaryHistory descentRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro jUnary uUnary mUnary sUnary tUnary pUnary _nUnary coverRoute cechRoute
    descentRoute replayRoute nameRoute namePkg
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed jUnary uUnary coverRoute
  have cechUnary : UnaryHistory C :=
    unary_cont_closed coverUnary mUnary cechRoute
  have descentUnary : UnaryHistory D :=
    unary_cont_closed cechUnary sUnary descentRoute
  have replayUnary : UnaryHistory R :=
    unary_cont_closed descentUnary tUnary replayRoute
  have nameUnary : UnaryHistory descentRead :=
    unary_cont_closed replayUnary pUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row descentRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row J ∨ hsame row U ∨ hsame row M ∨ hsame row C ∨ hsame row S ∨
              hsame row D ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨ hsame row N ∨
                hsame row coverRead ∨ hsame row descentRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J U coverRead ∧ Cont coverRead M C ∧
              Cont C S D ∧ Cont D T R ∧ Cont R P descentRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro descentRead ⟨hsame_refl descentRead, nameUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRoute, cechRoute, descentRoute, replayRoute, nameRoute,
          namePkg⟩
  }
  exact ⟨cert, coverUnary, cechUnary, descentUnary, replayUnary, nameUnary⟩

end BEDC.Derived.HypercoverUp
