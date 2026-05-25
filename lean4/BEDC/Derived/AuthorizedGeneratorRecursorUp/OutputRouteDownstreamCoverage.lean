import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorOutputRouteDownstreamCoverage [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead ledgerRead boundaryRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O A outputRead →
        Cont outputRead G ledgerRead →
          Cont ledgerRead N boundaryRead →
            Cont outputRead C downstreamRead →
              PkgSig bundle boundaryRead pkg →
                PkgSig bundle downstreamRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row boundaryRead ∨ hsame row downstreamRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row O ∨ hsame row A ∨ hsame row G ∨ hsame row C ∨
                          hsame row N ∨ hsame row boundaryRead ∨ hsame row downstreamRead)
                      (fun row : BHist =>
                        (hsame row boundaryRead ∨ hsame row downstreamRead) ∧
                          PkgSig bundle P pkg)
                      hsame ∧
                    UnaryHistory outputRead ∧ UnaryHistory ledgerRead ∧
                      UnaryHistory boundaryRead ∧ UnaryHistory downstreamRead ∧
                        hsame H (append A C) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier outputRoute ledgerRoute boundaryRoute downstreamRoute _boundaryPkg
    _downstreamPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH, unaryC,
      _unaryP, unaryG, unaryN, _carrierBranch, _carrierDescent, _carrierOutput,
      transportSame, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed outputReadUnary unaryG ledgerRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerReadUnary unaryN boundaryRoute
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed outputReadUnary unaryC downstreamRoute
  have sourceBoundary :
      (fun row : BHist =>
        (hsame row boundaryRead ∨ hsame row downstreamRead) ∧ UnaryHistory row)
        boundaryRead := by
    exact ⟨Or.inl (hsame_refl boundaryRead), boundaryReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row boundaryRead ∨ hsame row downstreamRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row A ∨ hsame row G ∨ hsame row C ∨ hsame row N ∨
              hsame row boundaryRead ∨ hsame row downstreamRead)
          (fun row : BHist =>
            (hsame row boundaryRead ∨ hsame row downstreamRead) ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
        rcases source with ⟨surface, unaryRow⟩
        refine ⟨?_, unary_transport unaryRow same⟩
        rcases surface with sameBoundary | sameDownstream
        · exact Or.inl (hsame_trans (hsame_symm same) sameBoundary)
        · exact Or.inr (hsame_trans (hsame_symm same) sameDownstream)
    }
    pattern_sound := by
      intro row source
      rcases source.left with sameBoundary | sameDownstream
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameBoundary)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameDownstream)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, outputReadUnary, ledgerReadUnary, boundaryReadUnary, downstreamReadUnary,
      transportSame, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
