import BMLean.Tables
import BMLean.Data.Hub052

namespace BMC

theorem hubOk_052 : hubChunkOk (parseRows BMD.hub052) = true := by native_decide

end BMC
