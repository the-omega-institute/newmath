import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N approxRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory A ->
        UnaryHistory L ->
          UnaryHistory T ->
            UnaryHistory E ->
              Cont B A M ->
                Cont M L S ->
                  Cont S T G ->
                    Cont G E approxRead ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row approxRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                                hsame row T ∨ hsame row S ∨ hsame row G ∨ hsame row E ∨
                                  hsame row approxRead ∨ hsame row N)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont B A M ∧ Cont M L S ∧ Cont S T G ∧
                                Cont G E approxRead ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory M ∧ UnaryHistory S ∧ UnaryHistory G ∧
                            UnaryHistory approxRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro boundaryUnary adjacencyUnary levelUnary toleranceUnary sealUnary boundaryRoute
    levelRoute toleranceRoute approximationRoute packageN
  have mediantUnary : UnaryHistory M :=
    unary_cont_closed boundaryUnary adjacencyUnary boundaryRoute
  have sternBrocotUnary : UnaryHistory S :=
    unary_cont_closed mediantUnary levelUnary levelRoute
  have approximationUnary : UnaryHistory G :=
    unary_cont_closed sternBrocotUnary toleranceUnary toleranceRoute
  have approxReadUnary : UnaryHistory approxRead :=
    unary_cont_closed approximationUnary sealUnary approximationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row approxRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
              hsame row S ∨ hsame row G ∨ hsame row E ∨ hsame row approxRead ∨
                hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A M ∧ Cont M L S ∧ Cont S T G ∧
              Cont G E approxRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro approxRead ⟨hsame_refl approxRead, approxReadUnary⟩
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
                    (Or.inr (Or.inr (Or.inl source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, levelRoute, toleranceRoute, approximationRoute,
          packageN⟩
  }
  exact ⟨cert, mediantUnary, sternBrocotUnary, approximationUnary, approxReadUnary⟩

end BEDC.Derived.FareySequenceUp
