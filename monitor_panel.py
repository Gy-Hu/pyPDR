from z3 import *
from rich.table import Table
from rich.panel import Panel
from rich.columns import Columns
import asciichartpy as acp
from rich.panel import Panel
import os
import csv
from datetime import datetime

class MonitorPannel:
    def __init__(self, pdr, enable_logging=True):
        self.pdr = pdr
        self.enable_logging = enable_logging
        self.time_stamp = datetime.now().strftime("%Y-%m-%d-%H:%M:%S")
        self.csv_file_path = self.get_csv_file_path() if enable_logging else None
        
    def get_csv_file_path(self):
        log_dir = "./logs/"
        os.makedirs(log_dir, exist_ok=True)
        return os.path.join(log_dir, f"pdr_log_{self.time_stamp}.csv")
    
    def write_to_csv(self, data):
        if self.enable_logging:
            file_exists = os.path.isfile(self.csv_file_path)
            with open(self.csv_file_path, "a", newline="") as csv_file:
                writer = csv.writer(csv_file)
                timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")
                for variable, value, percentage in data:
                    writer.writerow([timestamp, variable, value, percentage])

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
        table1.add_row(
            "Average CTI−induced clause size",
            (
                str(
                    # sum of all literals in all frames / number of clauses in all frames
                    sum(sum(frame.Lemma_size) for frame in self.pdr.frames)
                    /
                    # sum of all clauses in all frames
                    sum(len(frame.Lemma)-1 for frame in self.pdr.frames)
                )
                if sum(len(frame.Lemma)-1 for frame in self.pdr.frames) > 0
                else "0"
            ),
            "",
        )
        table1.add_row(
            "Average clauses per level",
            (
                str(
                    # sum of all clauses in all frames / number of frames
                    sum(len(frame.Lemma)-1 for frame in self.pdr.frames)
                    /
                    # number of frames
                    len(self.pdr.frames)
                )
                if len(self.pdr.frames) > 0
                else "0"
            ),
            "",
        )
            

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
        
        if self.pdr.status not in ["FOUND TRACE", "FOUND INV"] and self.enable_logging:
            # Collect the data
            data = [
                ["Engine Status", self.pdr.status, ""],
                ["Average Propagation Time (s)", f"{avg_prop_time:.2f}", ""],
                ["Average Predecessor Generalization Reduction (%)", f"{avg_gen_reduction:.2f}", ""],
                ["Average MIC Reduction (%)", f"{avg_mic_reduction:.2f}", ""],
                ["Sum of Propagation Time (s)", f"{self.pdr.sum_of_propagate_time:.2f}", percentage(self.pdr.sum_of_propagate_time)],
                ["Sum of Predecessor Generalization Time (s)", f"{self.pdr.sum_of_predecessor_generalization_time:.2f}", percentage(self.pdr.sum_of_predecessor_generalization_time)],
                ["Sum of MIC Time (s)", f"{self.pdr.sum_of_mic_time:.2f}", percentage(self.pdr.sum_of_mic_time)],
                ["Sum of CTI Producing Time (s)", f"{self.pdr.sum_of_cti_producing_time:.2f}", percentage(self.pdr.sum_of_cti_producing_time)],
                ["Sum of solve relative Time (s)", f"{self.pdr.sum_of_solve_relative_time:.2f}", percentage(self.pdr.sum_of_solve_relative_time)],
                ["Sum of check induction Time (s)", f"{self.pdr.sum_of_check_induction_time:.2f}", percentage(self.pdr.sum_of_check_induction_time)],
                ["Sum of frame trivially block Time (s)", f"{self.pdr.sum_of_frame_trivially_block_time:.2f}", percentage(self.pdr.sum_of_frame_trivially_block_time)],
                ["Sum of unsatcore reduce Time (s)", f"{self.pdr.sum_of_unsatcore_reduce_time:.2f}", percentage(self.pdr.sum_of_unsatcore_reduce_time)],
                ["Overall Runtime (s)", f"{self.pdr.overall_runtime:.2f}", ""],
                ["Total Push Attempts", str(self.pdr.total_push_attempts), ""],
                ["Overall Push Success Rate (%)", f"{overall_push_success_rate:.2f}", ""],
                ["Current Frame", str(len(self.pdr.frames) - 1), ""],
                ["Total Frames", str(len(self.pdr.frames)), ""],
                ["Total SAT Calls", str(self.pdr.sum_of_sat_call), ""],
                ["Average CTI−induced clause size", str(sum(sum(frame.Lemma_size) for frame in self.pdr.frames) / sum(len(frame.Lemma)-1 for frame in self.pdr.frames) if sum(len(frame.Lemma)-1 for frame in self.pdr.frames) > 0 else "0"), ""],
                ["Average clauses per level", str(sum(len(frame.Lemma)-1 for frame in self.pdr.frames) / len(self.pdr.frames) if len(self.pdr.frames) > 0 else "0"), ""]
            ]
            # Write the data to the csv file
            self.write_to_csv(data)

        return Columns([Panel(table1), 
                Panel(cti_plot, expand=False, title="~~ [bold][yellow]CTI Changes Vary to Time[/bold][/yellow] ~~"), 
                Panel(lemma_count_plot, expand=False, title="~~ [bold][cyan]Lemma Count Changes[/bold][/cyan] ~~"),
                table2])