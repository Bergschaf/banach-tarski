import os
import json

filename = "file_structure.json"

# Create a file structure
def elements(directory):
    elements = {x:None for x in os.listdir(directory)}
    for element in elements.copy():
        if os.path.isdir(directory + element):
            elements[element] = elements(directory + element + "/")
    return elements

# Write the file structure to a file (as json)
root_dirs = ["banach_tarski", "andere-Theoreme"]

file_structure = {x:elements(x + "/") for x in root_dirs}

with open(filename, "w") as f:
    json.dump(file_structure, f, indent=4)
