import BEDC.Derived.HilbertAlexanderBlockerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HilbertAlexanderBlockerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HilbertAlexanderBlockerCarrier [AskSetup] [PackageSetup]
    (S P T B F L A R C Q N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  hilbertAlexanderBlockerFields (HilbertAlexanderBlockerUp.mk S P T B F L A R C Q N) =
      [S, P, T, B, F, L, A, R, C, Q, N] ∧
    UnaryHistory S ∧ UnaryHistory P ∧ UnaryHistory T ∧ UnaryHistory B ∧
      UnaryHistory F ∧ UnaryHistory L ∧ UnaryHistory A ∧ UnaryHistory R ∧
        UnaryHistory C ∧ UnaryHistory Q ∧ UnaryHistory N ∧ PkgSig bundle N pkg

theorem HilbertAlexanderBlockerNameCertObligations [AskSetup] [PackageSetup]
    {S P T B F L A R C Q N blockerRead hilbertRead alexanderRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HilbertAlexanderBlockerCarrier S P T B F L A R C Q N bundle pkg ->
      Cont B F blockerRead ->
        Cont blockerRead L hilbertRead ->
          Cont hilbertRead A alexanderRead ->
            Cont alexanderRead N named ->
              PkgSig bundle named pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row named ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row P ∨ hsame row T ∨ hsame row B ∨
                      hsame row F ∨ hsame row L ∨ hsame row A ∨ hsame row named)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B F blockerRead ∧
                      Cont blockerRead L hilbertRead ∧
                        Cont hilbertRead A alexanderRead ∧ PkgSig bundle named pkg)
                  hsame ∧ UnaryHistory blockerRead ∧ UnaryHistory hilbertRead ∧
                    UnaryHistory alexanderRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier blockerRoute hilbertRoute alexanderRoute namedRoute namedPkg
  obtain ⟨_fields, _simplicialUnary, _polynomialUnary, _traceUnary, boundaryUnary,
    blockerUnaryBase, hilbertUnaryBase, alexanderUnaryBase, _transportUnary,
    _continuationUnary, _provenanceUnary, nameUnary, _namePkg⟩ := carrier
  have blockerUnary : UnaryHistory blockerRead :=
    unary_cont_closed boundaryUnary blockerUnaryBase blockerRoute
  have hilbertUnary : UnaryHistory hilbertRead :=
    unary_cont_closed blockerUnary hilbertUnaryBase hilbertRoute
  have alexanderUnary : UnaryHistory alexanderRead :=
    unary_cont_closed hilbertUnary alexanderUnaryBase alexanderRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed alexanderUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row named ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row P ∨ hsame row T ∨ hsame row B ∨ hsame row F ∨
            hsame row L ∨ hsame row A ∨ hsame row named)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont B F blockerRead ∧ Cont blockerRead L hilbertRead ∧
            Cont hilbertRead A alexanderRead ∧ PkgSig bundle named pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, blockerRoute, hilbertRoute, alexanderRoute, namedPkg⟩
  }
  exact ⟨cert, blockerUnary, hilbertUnary, alexanderUnary, namedUnary⟩

end BEDC.Derived.HilbertAlexanderBlockerUp
