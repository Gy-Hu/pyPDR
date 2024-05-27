from z3 import *
from rich.table import Table
from rich.panel import Panel
from rich.columns import Columns
import asciichartpy as acp
from rich.panel import Panel

class MonitorPannel:
    def __init__(self, pdr):
        self.pdr = pdr
    def get_table(self):
        table1 = Table(title="PDR Algorithm Status")
        table1.add_column("Variable", style="cyan")
        table1.add_column("Value", style="magenta")
        table1.add_column("Percentage (%)", style="green")

        table1.add_row("Engine Status", self.pdr.status, "")
        avg_prop_time = sum(self.pdr.avg_propagation_times) / len(self.pdr.avg_propagation_times) if self.pdr.avg_propagation_times else 0
        avg_gen_reduction = sum(self.pdr.predecessor_generalization_reduction_percentages) / len(self.pdr.predecessor_generalization_reduction_percentages) if self.pdr.predecessor_generalization_reduction_percentages else 0
        avg_mic_reduction = sum(self.pdr.mic_reduction_percentages) / len(self.pdr.mic_reduction_percentages) if self.pdr.mic_reduction_percentages else 0

        table1.add_row("Average Propagation Time (s)", f"{avg_prop_time:.2f}", "")
        table1.add_row("Average Predecessor Generalization Reduction (%)", f"{avg_gen_reduction:.2f}", "")
        table1.add_row("Average MIC Reduction (%)", f"{avg_mic_reduction:.2f}", "")

        def percentage(value):
            return f"{value / self.pdr.overall_runtime * 100:.2f}" if self.pdr.overall_runtime != 0 else "0.00"

        table1.add_row("Sum of Propagation Time (s)", f"{self.pdr.sum_of_propagate_time:.2f}", percentage(self.pdr.sum_of_propagate_time))
        table1.add_row("Sum of Predecessor Generalization Time (s)", f"{self.pdr.sum_of_predecessor_generalization_time:.2f}", percentage(self.pdr.sum_of_predecessor_generalization_time))
        table1.add_row("Sum of MIC Time (s)", f"{self.pdr.sum_of_mic_time:.2f}", percentage(self.pdr.sum_of_mic_time))
        table1.add_row("Sum of CTI Producing Time (s)", f"{self.pdr.sum_of_cti_producing_time:.2f}", percentage(self.pdr.sum_of_cti_producing_time))
        table1.add_row("Sum of solve relative Time (s)", f"{self.pdr.sum_of_solve_relative_time:.2f}", percentage(self.pdr.sum_of_solve_relative_time))
        table1.add_row("Sum of check induction Time (s)", f"{self.pdr.sum_of_check_induction_time:.2f}", percentage(self.pdr.sum_of_check_induction_time))
        table1.add_row("Sum of frame trivially block Time (s)", f"{self.pdr.sum_of_frame_trivially_block_time:.2f}", percentage(self.pdr.sum_of_frame_trivially_block_time))
        table1.add_row("Sum of unsatcore reduce Time (s)", f"{self.pdr.sum_of_unsatcore_reduce_time:.2f}", percentage(self.pdr.sum_of_unsatcore_reduce_time))

        table1.add_row("Overall Runtime (s)", f"{self.pdr.overall_runtime:.2f}", "")
        overall_push_success_rate = (self.pdr.successful_pushes / self.pdr.total_push_attempts * 100) if self.pdr.total_push_attempts > 0 else 0
        table1.add_row("Total Push Attempts", str(self.pdr.total_push_attempts), "")
        table1.add_row("Overall Push Success Rate (%)", f"{overall_push_success_rate:.2f}", "")
        table1.add_row("Current Frame", str(len(self.pdr.frames) - 1), "")
        table1.add_row("Total Frames", str(len(self.pdr.frames)), "")
        table1.add_row("Total SAT Calls", str(self.pdr.sum_of_sat_call), "")

        
        
        table2 = Table(title="Frame Information")
        table2.add_column("Frame", style="cyan")
        table2.add_column("Size", style="magenta")
        table2.add_column("Pushed", style="green")
        table2.add_column("Ratio", style="yellow")

        # Display information for the latest 17 frames
        start_frame = max(1, len(self.pdr.frames) - 17)
        for index in range(start_frame, len(self.pdr.frames)):
            push_cnt = self.pdr.frames[index].pushed.count(True)
            table2.add_row(f"{index}", str(len(self.pdr.frames[index].Lemma)), str(push_cnt), f"{push_cnt / len(self.pdr.frames[index].Lemma) * 100:.2f}") if len(self.pdr.frames[index].Lemma) > 0 else table2.add_row(f"{index}", "0", "0", "0")
            
        # Create a line plot for CTI queue size changes
        cti_plot = acp.plot(self.pdr.cti_queue_sizes[-20:])
        
        # Create a line plot for lemma count changes
        lemma_counts = [len(frame.Lemma) for frame in self.pdr.frames[1:]]
        frame_numbers = list(range(1, len(self.pdr.frames)))
        lemma_count_plot = acp.plot(lemma_counts[:], {'height': 5, 'X': len(self.pdr.frames)})

        return Columns([Panel(table1), 
                Panel(cti_plot, expand=False, title="~~ [bold][yellow]CTI Changes Vary to Time[/bold][/yellow] ~~"), 
                Panel(lemma_count_plot, expand=False, title="~~ [bold][cyan]Lemma Count Changes[/bold][/cyan] ~~"),
                table2])