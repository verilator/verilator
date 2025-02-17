import re
from collections import defaultdict

class SignalBit:
    def __init__(self):
        self.last_val = 0
        self.high_time = 0
        self.transitions = 0

    def aggregate(self, dt, new_val):
        if int(new_val) != int(self.last_val):
            self.transitions += 1
        
        if self.last_val:
            self.high_time += dt

        self.last_val = new_val

class Signal:
    def __init__(self, signal_name, signal_width):
        self.name = signal_name
        self.width = signal_width

        self.bits = []
        for _ in range(self.width):
            self.bits.append(SignalBit())

        self.last_time = 0


class VCDParser:
    def __init__(self):
        self.signal_definitions = {}
        self.current_time = 0

    def parse(self, vcd_filename):
        with open(vcd_filename, 'r') as vcd_file:
            for line in vcd_file:
                line = line.strip()
                if not line:
                    continue
                
                match = re.match(r'\$var\s+(\w+)\s+(\d+)\s+(\S+)\s+(\S+)\s*(\S*)\s*\$end', line)
                if match:
                    _, signal_width, signal_id, signal_name, _ = match.groups()
                    self.signal_definitions[signal_id] = Signal(signal_name, int(signal_width))
                    continue

                match = re.match(r'\#(\d+)', line)
                if match:
                    timestamp = match.groups()
                    self.current_time = int(timestamp[0])
                    continue

                match = re.match(r'b(\d+)\s+(\S+)', line)
                if match:
                    value, signal_id = match.groups()

                    dt = self.current_time - self.signal_definitions[signal_id].last_time
                    self.signal_definitions[signal_id].last_time = self.current_time

                    index = 0
                    for bit in reversed(value):
                        self.signal_definitions[signal_id].bits[index].aggregate(dt, int(bit))
                        index += 1

                    continue
        
                match = re.match(r'(\d+)(\S+)', line)
                if match:
                    value, signal_id = match.groups()
                    
                    dt = self.current_time - self.signal_definitions[signal_id].last_time
                    self.signal_definitions[signal_id].last_time = self.current_time

                    self.signal_definitions[signal_id].bits[0].aggregate(dt, int(value))


def generate_saif(vcd_parser, saif_filename):
    with open(saif_filename, 'w') as saif_file:
        for _, activity in vcd_parser.signal_definitions.items():
            index = 0
            for activity_bit in activity.bits:
                if activity_bit.transitions <= 0:
                    index += 1
                    continue

                if activity_bit.last_val == 1:
                    activity_bit.high_time += vcd_parser.current_time - activity.last_time

                if activity.width <= 1:
                    saif_file.write(f"{activity.name} (T0 {vcd_parser.current_time - activity_bit.high_time}) (T1 {activity_bit.high_time}) (TZ 0) (TX 0) (TB 0) (TC {activity_bit.transitions})\n")
                else:    
                    saif_file.write(f"{activity.name}[{index}] (T0 {vcd_parser.current_time - activity_bit.high_time}) (T1 {activity_bit.high_time}) (TZ 0) (TX 0) (TB 0) (TC {activity_bit.transitions})\n")
                index += 1

def vcd_to_saif(vcd_filename, saif_filename):
    vcd_parser = VCDParser()

    vcd_parser.parse(vcd_filename)
    generate_saif(vcd_parser, saif_filename)

vcd_to_saif('input.vcd', 'output.saif')