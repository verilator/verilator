import re
from collections import defaultdict

class SAIFSignalBit:
    def __init__(self):
        self.last_val = 0
        self.high_time = 0
        self.low_time = 0
        self.transitions = 0

    def aggregate(self, dt, new_val):
        if int(new_val) != int(self.last_val):
            self.transitions += 1
        
        if self.last_val:
            self.high_time += dt

        self.last_val = new_val

class SAIFSignal:
    def __init__(self, signal_name, signal_width = 0):
        self.name = signal_name
        self.width = signal_width
        self.last_time = 0

        self.bits = []
        for _ in range(self.width):
            self.bits.append(SAIFSignalBit())


class VCDToSAIFParser:
    def __init__(self):
        self.signal_definitions = {}
        self.signal_indirections = {}
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
                    self.signal_indirections[signal_id] = signal_name
                    self.signal_definitions[signal_name] = SAIFSignal(signal_name, int(signal_width))
                    continue

                match = re.match(r'\#(\d+)', line)
                if match:
                    timestamp = match.groups()
                    self.current_time = int(timestamp[0])
                    continue

                match = re.match(r'b(\d+)\s+(\S+)', line)
                if match:
                    value, signal_id = match.groups()

                    dt = self.current_time - self.signal_definitions[self.signal_indirections[signal_id]].last_time
                    self.signal_definitions[self.signal_indirections[signal_id]].last_time = self.current_time

                    index = 0
                    for bit in reversed(value):
                        self.signal_definitions[self.signal_indirections[signal_id]].bits[index].aggregate(dt, int(bit))
                        index += 1

                    continue
        
                match = re.match(r'(\d+)(\S+)', line)
                if match:
                    value, signal_id = match.groups()
                    
                    dt = self.current_time - self.signal_definitions[self.signal_indirections[signal_id]].last_time
                    self.signal_definitions[self.signal_indirections[signal_id]].last_time = self.current_time

                    self.signal_definitions[self.signal_indirections[signal_id]].bits[0].aggregate(dt, int(value))

            for _, signal in self.signal_definitions.items():
                for i in range(signal.width):
                    if signal.bits[i].last_val == 1:
                        signal.bits[i].high_time += self.current_time - signal.last_time

                    signal.bits[i].low_time = self.current_time - signal.bits[i].high_time


class SAIFParser:
    def __init__(self):
        self.signal_definitions = {}

    def parse(self, saif_filename):
        with open(saif_filename, 'r') as saif_file:
            for line in saif_file:
                line = line.strip()
                if not line:
                    continue

                match = re.search(r'(\w+)\[*(\d*)\]*\s+(\(T(.+)\))+', line)
                if match:
                    signal_name, bit_index, bit_values, _ = match.groups()

                    if bit_index == '':
                        bit_index = 0

                    if signal_name not in self.signal_definitions:
                        self.signal_definitions[signal_name] = SAIFSignal(signal_name)

                    for _ in range(0, int(bit_index) - self.signal_definitions[signal_name].width + 1):
                        self.signal_definitions[signal_name].bits.append(SAIFSignalBit())
                        
                    self.signal_definitions[signal_name].width = int(bit_index) + 1

                    match = re.search(r'T0 (\d+)', bit_values)
                    if match:
                        low_time = match.groups()[0]

                        self.signal_definitions[signal_name].bits[int(bit_index)].low_time = low_time

                    match = re.search(r'T1 (\d+)', bit_values)
                    if match:
                        high_time = match.groups()[0]
                        
                        self.signal_definitions[signal_name].bits[int(bit_index)].high_time = high_time

                    match = re.search(r'TC (\d+)', bit_values)
                    if match:
                        toggle_count = match.groups()[0]
                        
                        self.signal_definitions[signal_name].bits[int(bit_index)].transitions = toggle_count

vcd_to_saif_parser = VCDToSAIFParser()
vcd_to_saif_parser.parse("simx.vcd")

saif_parser = SAIFParser()
saif_parser.parse("simx.saif")

print("From VCD")
for signal_name, signal in vcd_to_saif_parser.signal_definitions.items():
    for bit in range(signal.width):
        print(f"{signal.name}[{bit}] (T0 {signal.bits[bit].low_time}) (T1 {signal.bits[bit].high_time}) (TC {signal.bits[bit].transitions})")

print()

print("From SAIF")
for signal_name, signal in saif_parser.signal_definitions.items():
    for bit in range(signal.width):
        print(f"{signal.name}[{bit}] (T0 {signal.bits[bit].low_time}) (T1 {signal.bits[bit].high_time}) (TC {signal.bits[bit].transitions})")