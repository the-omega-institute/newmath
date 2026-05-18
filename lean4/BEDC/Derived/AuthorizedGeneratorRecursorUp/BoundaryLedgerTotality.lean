import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBoundaryLedgerTotality [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead ledgerRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead G ledgerRead ->
          Cont ledgerRead N boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory G ∧ UnaryHistory N ∧
                UnaryHistory outputRead ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory boundaryRead ∧ Cont O A outputRead ∧
                    Cont outputRead G ledgerRead ∧ Cont ledgerRead N boundaryRead ∧
                      hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier outputRoute ledgerRoute boundaryRoute boundaryPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      _unaryC, _unaryP, unaryG, unaryN, _carrierBranch, _carrierDescent,
      _carrierOutput, transportSame, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed outputReadUnary unaryG ledgerRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerReadUnary unaryN boundaryRoute
  exact
    ⟨unaryO, unaryA, unaryG, unaryN, outputReadUnary, ledgerReadUnary,
      boundaryReadUnary, outputRoute, ledgerRoute, boundaryRoute, transportSame,
      provenancePkg, boundaryPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
