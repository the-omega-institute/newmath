import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitSelectorBudgetFinitePrefixBudgetPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      prefixWindow prefixReadback prefixSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont windows dyadic prefixWindow →
        Cont prefixWindow readback prefixReadback →
          Cont prefixReadback realSeal prefixSeal →
            PkgSig bundle prefixSeal pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row windows ∨ hsame row dyadic ∨ hsame row readback ∨
                    hsame row realSeal ∨ hsame row prefixSeal)
                (fun row : BHist =>
                  Cont windows dyadic prefixWindow ∧
                    Cont prefixWindow readback prefixReadback ∧
                      Cont prefixReadback realSeal prefixSeal ∧
                        (hsame row windows ∨ hsame row dyadic ∨ hsame row readback ∨
                          hsame row realSeal ∨ hsame row prefixSeal))
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle prefixSeal pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier windowsDyadicPrefix prefixWindowReadback prefixReadbackRealSeal prefixSealPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have prefixWindowUnary : UnaryHistory prefixWindow :=
    unary_cont_closed windowsUnary dyadicUnary windowsDyadicPrefix
  have prefixReadbackUnary : UnaryHistory prefixReadback :=
    unary_cont_closed prefixWindowUnary readbackUnary prefixWindowReadback
  have prefixSealUnary : UnaryHistory prefixSeal :=
    unary_cont_closed prefixReadbackUnary realSealUnary prefixReadbackRealSeal
  exact {
    core := {
      carrier_inhabited := Exists.intro windows (Or.inl (hsame_refl windows))
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
        intro row other same source
        cases source with
        | inl rowWindows =>
            exact Or.inl (hsame_trans (hsame_symm same) rowWindows)
        | inr tail =>
            cases tail with
            | inl rowDyadic =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowDyadic))
            | inr tail =>
                cases tail with
                | inl rowReadback =>
                    exact
                      Or.inr (Or.inr (Or.inl
                        (hsame_trans (hsame_symm same) rowReadback)))
                | inr tail =>
                    cases tail with
                    | inl rowRealSeal =>
                        exact
                          Or.inr (Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm same) rowRealSeal))))
                    | inr rowPrefixSeal =>
                        exact
                          Or.inr (Or.inr (Or.inr (Or.inr
                            (hsame_trans (hsame_symm same) rowPrefixSeal))))
    }
    pattern_sound := by
      intro _row source
      exact ⟨windowsDyadicPrefix, prefixWindowReadback, prefixReadbackRealSeal, source⟩
    ledger_sound := by
      intro row source
      cases source with
      | inl rowWindows =>
          exact ⟨unary_transport windowsUnary (hsame_symm rowWindows), prefixSealPkg⟩
      | inr tail =>
          cases tail with
          | inl rowDyadic =>
              exact ⟨unary_transport dyadicUnary (hsame_symm rowDyadic), prefixSealPkg⟩
          | inr tail =>
              cases tail with
              | inl rowReadback =>
                  exact
                    ⟨unary_transport readbackUnary (hsame_symm rowReadback),
                      prefixSealPkg⟩
              | inr tail =>
                  cases tail with
                  | inl rowRealSeal =>
                      exact
                        ⟨unary_transport realSealUnary (hsame_symm rowRealSeal),
                          prefixSealPkg⟩
                  | inr rowPrefixSeal =>
                      exact
                        ⟨unary_transport prefixSealUnary (hsame_symm rowPrefixSeal),
                          prefixSealPkg⟩
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
