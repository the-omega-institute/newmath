import BEDC.Derived.FareySequenceUp.NameCertObligations

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceMediantDensityWindow [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E _H _C P N densityRead approxRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B →
      UnaryHistory A →
        UnaryHistory L →
          UnaryHistory T →
            UnaryHistory D →
              UnaryHistory Q →
                UnaryHistory W →
                  UnaryHistory R →
                    UnaryHistory G →
                      UnaryHistory E →
                        Cont B A M →
                          Cont M L S →
                            Cont S D densityRead →
                              Cont densityRead Q approxRead →
                                Cont approxRead W R →
                                  Cont R G realRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row realRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row M ∨ hsame row S ∨
                                                hsame row densityRead ∨
                                                  hsame row approxRead ∨ hsame row R ∨
                                                    hsame row realRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont B A M ∧
                                                Cont M L S ∧ Cont S D densityRead ∧
                                                  Cont densityRead Q approxRead ∧
                                                    Cont approxRead W R ∧
                                                      Cont R G realRead ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle N pkg)
                                            hsame ∧
                                          UnaryHistory M ∧ UnaryHistory S ∧
                                            UnaryHistory densityRead ∧
                                              UnaryHistory approxRead ∧
                                                UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro boundaryUnary adjacencyUnary levelUnary _toleranceUnary densityUnary rationalUnary
    streamUnary _regseqUnary approximationUnary _realSealUnary boundaryRoute levelRoute densityRoute
    approximationRoute streamRoute realRoute packageP packageN
  have mediantUnary : UnaryHistory M :=
    unary_cont_closed boundaryUnary adjacencyUnary boundaryRoute
  have sternBrocotUnary : UnaryHistory S :=
    unary_cont_closed mediantUnary levelUnary levelRoute
  have densityReadUnary : UnaryHistory densityRead :=
    unary_cont_closed sternBrocotUnary densityUnary densityRoute
  have approxReadUnary : UnaryHistory approxRead :=
    unary_cont_closed densityReadUnary rationalUnary approximationRoute
  have regseqReadUnary : UnaryHistory R :=
    unary_cont_closed approxReadUnary streamUnary streamRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqReadUnary approximationUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row S ∨ hsame row densityRead ∨ hsame row approxRead ∨
              hsame row R ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A M ∧ Cont M L S ∧ Cont S D densityRead ∧
              Cont densityRead Q approxRead ∧ Cont approxRead W R ∧ Cont R G realRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
                (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, levelRoute, densityRoute, approximationRoute,
          streamRoute, realRoute, packageP, packageN⟩
  }
  exact
    ⟨cert, mediantUnary, sternBrocotUnary, densityReadUnary, approxReadUnary,
      realReadUnary⟩

end BEDC.Derived.FareySequenceUp
