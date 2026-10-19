import BMLean.Tables
import BMLean.Data.Hub048

namespace BMC

theorem hubOk_048 : hubChunkOk (parseRows BMD.hub048) = true := by native_decide

end BMC
