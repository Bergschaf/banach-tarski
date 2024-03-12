import os
import json

filename = "file_structure.json"

# Create a file structure
def elements(directory):
    elements_ = {x:None for x in os.listdir(directory)}
    for element in elements_.copy():
        if os.path.isdir(directory + element):
            elements_[element] = elements(directory + element + "/")
    return elements_

# Write the file structure to a file (as json)
root_dirs = ["banach_tarski", "andere-Theoreme"]

file_structure = {x:elements(x + "/") for x in root_dirs}

with open(filename, "w") as f:
    json.dump(file_structure, f, indent=4)
