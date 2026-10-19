import BMLean.Tables
import BMLean.Data.Hub022

namespace BMC

theorem hubOk_022 : hubChunkOk (parseRows BMD.hub022) = true := by native_decide

end BMC
