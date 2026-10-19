import BMLean.Tables
import BMLean.Data.Hub012

namespace BMC

theorem hubOk_012 : hubChunkOk (parseRows BMD.hub012) = true := by native_decide

end BMC
