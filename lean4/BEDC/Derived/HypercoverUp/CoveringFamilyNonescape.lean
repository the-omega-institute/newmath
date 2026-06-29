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

theorem HypercoverCarrier_covering_family_nonescape [AskSetup] [PackageSetup]
    {J U M C S D T R P N coverRead matchingRead cechRead sheafRead descentRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory J →
      UnaryHistory U →
        UnaryHistory M →
          UnaryHistory C →
            UnaryHistory S →
              UnaryHistory D →
                UnaryHistory T →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont J U coverRead →
                        Cont coverRead M matchingRead →
                          Cont matchingRead C cechRead →
                            Cont cechRead S sheafRead →
                              Cont sheafRead D descentRead →
                                Cont descentRead T R →
                                  Cont R P namedRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row J ∨ hsame row U ∨ hsame row M ∨
                                                hsame row C ∨ hsame row S ∨
                                                  hsame row D ∨ hsame row T ∨
                                                    hsame row R ∨ hsame row P ∨
                                                      hsame row N ∨
                                                        hsame row coverRead ∨
                                                          hsame row matchingRead ∨
                                                            hsame row cechRead ∨
                                                              hsame row sheafRead ∨
                                                                hsame row descentRead ∨
                                                                  hsame row namedRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont J U coverRead ∧
                                                Cont coverRead M matchingRead ∧
                                                  Cont matchingRead C cechRead ∧
                                                    Cont cechRead S sheafRead ∧
                                                      Cont sheafRead D descentRead ∧
                                                        Cont descentRead T R ∧
                                                          Cont R P namedRead ∧
                                                            PkgSig bundle P pkg ∧
                                                              PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory coverRead ∧
                                            UnaryHistory matchingRead ∧
                                              UnaryHistory cechRead ∧
                                                UnaryHistory sheafRead ∧
                                                  UnaryHistory descentRead ∧
                                                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro jUnary uUnary mUnary cUnary sUnary dUnary tUnary pUnary _nUnary
    coverRoute matchingRoute cechRoute sheafRoute descentRoute replayRoute namedRoute
    pPkg nPkg
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed jUnary uUnary coverRoute
  have matchingUnary : UnaryHistory matchingRead :=
    unary_cont_closed coverUnary mUnary matchingRoute
  have cechUnary : UnaryHistory cechRead :=
    unary_cont_closed matchingUnary cUnary cechRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed cechUnary sUnary sheafRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed sheafUnary dUnary descentRoute
  have replayUnary : UnaryHistory R :=
    unary_cont_closed descentUnary tUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary pUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row J ∨ hsame row U ∨ hsame row M ∨ hsame row C ∨ hsame row S ∨
              hsame row D ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨
                hsame row N ∨ hsame row coverRead ∨ hsame row matchingRead ∨
                  hsame row cechRead ∨ hsame row sheafRead ∨
                    hsame row descentRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J U coverRead ∧ Cont coverRead M matchingRead ∧
              Cont matchingRead C cechRead ∧ Cont cechRead S sheafRead ∧
                Cont sheafRead D descentRead ∧ Cont descentRead T R ∧
                  Cont R P namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
        ⟨source.right, coverRoute, matchingRoute, cechRoute, sheafRoute,
          descentRoute, replayRoute, namedRoute, pPkg, nPkg⟩
  }
  exact
    ⟨cert, coverUnary, matchingUnary, cechUnary, sheafUnary, descentUnary,
      namedUnary⟩

end BEDC.Derived.HypercoverUp
