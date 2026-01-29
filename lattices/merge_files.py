from genus import write_header_to_file, COL_TYPE_LATTICE_GENUS, COL_TYPE_LATTICE, FIELDS_LATTICE_GENUS,FIELDS_LATTICE 

def merge_files(fnames, out_fname, schema="lat_genera"):
    col_type = COL_TYPE_LATTICE_GENUS if (schema == "lat_genera") else COL_TYPE_LATTICE
    fields = FIELDS_LATTICE_GENUS if (schema == "lat_genera") else FIELDS_LATTICE
    write_header_to_file(out_fname, col_type=col_type, fields=fields)
    for fname in fnames:
        with open(fname) as f:
        # only needed if they have headers
        #    lines = f.readlines()[3:]
            lines = f.readlines()
        with open(out_fname, "a") as f:
            f.writelines(lines)
