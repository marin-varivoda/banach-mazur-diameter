import BMLean.Tables
import BMLean.Data.Hub013

namespace BMC

theorem hubOk_013 : hubChunkOk (parseRows BMD.hub013) = true := by native_decide

end BMC
