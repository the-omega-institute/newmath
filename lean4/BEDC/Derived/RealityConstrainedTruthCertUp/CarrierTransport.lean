import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RealityConstrainedTruthCertCarrier_transport [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N sourceSig classifierRead ledgerFailure localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S Sigma sourceSig ->
      Cont sourceSig K classifierRead ->
        Cont L F ledgerFailure ->
          Cont ledgerFailure N localRead ->
            PkgSig bundle localRead pkg ->
              TasteGate.realityConstrainedTruthCertFields
                  (TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N) =
                [S, Sigma, K, T, U, D, I, L, F, N] /\
              Cont S Sigma sourceSig /\
                Cont sourceSig K classifierRead /\
                  Cont L F ledgerFailure /\
                    Cont ledgerFailure N localRead /\
                      PkgSig bundle localRead pkg /\
                        SemanticNameCert
                          (fun row : BHist => hsame row localRead)
                          (fun row : BHist =>
                            hsame row sourceSig \/ hsame row classifierRead \/
                              hsame row ledgerFailure \/ hsame row localRead)
                          (fun row : BHist =>
                            hsame row localRead /\ PkgSig bundle localRead pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro sourceRoute classifierRoute ledgerRoute localRoute localPkg
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row localRead)
        (fun row : BHist =>
          hsame row sourceSig \/ hsame row classifierRead \/ hsame row ledgerFailure \/
            hsame row localRead)
        (fun row : BHist => hsame row localRead /\ PkgSig bundle localRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro localRead (hsame_refl localRead)
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
          exact hsame_trans (hsame_symm sameRows) source
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source))
      ledger_sound := by
        intro _row source
        exact ⟨source, localPkg⟩
    }
  exact
    ⟨rfl, sourceRoute, classifierRoute, ledgerRoute, localRoute, localPkg, cert⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
