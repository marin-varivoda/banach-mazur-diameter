import BMLean.Tables
import BMLean.Data.Hub044

namespace BMC

theorem hubOk_044 : hubChunkOk (parseRows BMD.hub044) = true := by native_decide

end BMC
