import BMLean.Tables
import BMLean.Data.Hub003

namespace BMC

theorem hubOk_003 : hubChunkOk (parseRows BMD.hub003) = true := by native_decide

end BMC
