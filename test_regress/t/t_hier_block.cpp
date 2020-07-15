
extern "C" int dpi_export_func();

extern "C" int dpi_import_func() {
    return dpi_export_func() - 1;
}
