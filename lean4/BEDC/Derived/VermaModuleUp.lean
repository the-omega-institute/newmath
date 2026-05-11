import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.VermaModuleUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem VermaModuleFiniteCarrier_obligation_surface
    {lie root highest action generator provenance endpoint : BHist} :
    UnaryHistory lie ->
      UnaryHistory root ->
        UnaryHistory action ->
          UnaryHistory provenance ->
            Cont lie root highest ->
              Cont highest action generator ->
                Cont generator provenance endpoint ->
                  UnaryHistory highest ∧ UnaryHistory generator ∧ UnaryHistory endpoint ∧
                    hsame highest (append lie root) ∧
                      hsame generator (append highest action) ∧
                        hsame endpoint (append generator provenance) := by
  intro lieUnary rootUnary actionUnary provenanceUnary lieRootHighest highestActionGenerator
  intro generatorProvenanceEndpoint
  have highestUnary : UnaryHistory highest :=
    unary_cont_closed lieUnary rootUnary lieRootHighest
  have generatorUnary : UnaryHistory generator :=
    unary_cont_closed highestUnary actionUnary highestActionGenerator
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed generatorUnary provenanceUnary generatorProvenanceEndpoint
  exact And.intro highestUnary
    (And.intro generatorUnary
      (And.intro endpointUnary
        (And.intro lieRootHighest
          (And.intro highestActionGenerator generatorProvenanceEndpoint))))

end BEDC.Derived.VermaModuleUp
