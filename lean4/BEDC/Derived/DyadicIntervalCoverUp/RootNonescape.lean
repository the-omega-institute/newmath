import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootNonescape [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead coverRead sealRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U endpointRead →
        Cont M R coverRead →
          Cont coverRead A sealRead →
            Cont sealRead N rootRead →
              PkgSig bundle rootRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                        hsame row A ∨ hsame row N ∨ hsame row endpointRead ∨
                          hsame row coverRead ∨ hsame row sealRead ∨ hsame row rootRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont L U endpointRead ∧ Cont M R coverRead ∧
                        Cont coverRead A sealRead ∧ Cont sealRead N rootRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle rootRead pkg)
                    hsame ∧
                  UnaryHistory endpointRead ∧ UnaryHistory coverRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro surface endpointCont coverCont sealCont rootCont rootPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointCont
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealCont
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sealUnary nUnary rootCont
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row A ∨
            hsame row N ∨ hsame row endpointRead ∨ hsame row coverRead ∨
              hsame row sealRead ∨ hsame row rootRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont L U endpointRead ∧ Cont M R coverRead ∧
            Cont coverRead A sealRead ∧ Cont sealRead N rootRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle rootRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro rootRead (And.intro (hsame_refl rootRead) rootUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact And.intro (hsame_trans (hsame_symm same) source.left)
          (unary_transport source.right same)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointCont, coverCont, sealCont, rootCont, pPkg, rootPkg⟩
  }
  exact ⟨cert, endpointUnary, coverUnary, sealUnary, rootUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
