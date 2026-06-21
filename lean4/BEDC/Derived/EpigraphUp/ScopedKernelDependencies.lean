import BEDC.Derived.EpigraphUp.CarrierRowTransportSurface

namespace BEDC.Derived.EpigraphUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EpigraphScopedKernelDependencies [AskSetup] [PackageSetup]
    {D V L O H C P N valueRead lowerRead epigraphRead transportedRead replayRead
      ledgerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EpigraphContPkgCarrier D V L O H C P N bundle pkg ->
      Cont D V valueRead ->
        Cont valueRead L lowerRead ->
          Cont lowerRead O epigraphRead ->
            Cont epigraphRead H transportedRead ->
              Cont transportedRead C replayRead ->
                Cont replayRead P ledgerRead ->
                  Cont ledgerRead N namedRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨
                                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                                  hsame row valueRead ∨ hsame row lowerRead ∨
                                    hsame row epigraphRead ∨ hsame row transportedRead ∨
                                      hsame row replayRead ∨ hsame row ledgerRead ∨
                                        hsame row namedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont D V valueRead ∧
                                Cont valueRead L lowerRead ∧ Cont lowerRead O epigraphRead ∧
                                  Cont epigraphRead H transportedRead ∧
                                    Cont transportedRead C replayRead ∧
                                      Cont replayRead P ledgerRead ∧
                                        Cont ledgerRead N namedRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory valueRead ∧ UnaryHistory lowerRead ∧
                            UnaryHistory epigraphRead ∧ UnaryHistory transportedRead ∧
                              UnaryHistory replayRead ∧ UnaryHistory ledgerRead ∧
                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier valueRoute lowerRoute epigraphRoute transportRoute replayRoute ledgerRoute
    nameRoute provenancePkg namePkg
  obtain ⟨dUnary, vUnary, lUnary, oUnary, hUnary, cUnary, pUnary, nUnary,
    _carrierValueRoute, _carrierTransportRoute, _carrierProvenancePkg,
      _carrierNamePkg⟩ := carrier
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed dUnary vUnary valueRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed valueUnary lUnary lowerRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed lowerUnary oUnary epigraphRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed epigraphUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary cUnary replayRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed replayUnary pUnary ledgerRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row valueRead ∨
                hsame row lowerRead ∨ hsame row epigraphRead ∨ hsame row transportedRead ∨
                  hsame row replayRead ∨ hsame row ledgerRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D V valueRead ∧ Cont valueRead L lowerRead ∧
              Cont lowerRead O epigraphRead ∧ Cont epigraphRead H transportedRead ∧
                Cont transportedRead C replayRead ∧ Cont replayRead P ledgerRead ∧
                  Cont ledgerRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, valueRoute, lowerRoute, epigraphRoute, transportRoute, replayRoute,
          ledgerRoute, nameRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, valueUnary, lowerUnary, epigraphUnary, transportedUnary, replayUnary,
      ledgerUnary, namedUnary⟩

end BEDC.Derived.EpigraphUp
