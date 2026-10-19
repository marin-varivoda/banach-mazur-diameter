import BMLean.Tables
import BMLean.Data.Hub051

namespace BMC

theorem hubOk_051 : hubChunkOk (parseRows BMD.hub051) = true := by native_decide

end BMC
