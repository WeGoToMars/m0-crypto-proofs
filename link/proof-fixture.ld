/*
 * Proof fixture linker script (not a bootable board image).
 *
 * The entry symbol is passed with -e by tools/build.sh.
 * Places .text at the MSPM0L2228 SRAM base so the proved addresses match an
 * SRAM-execution profile. Board bring-up needs a separate script with a vector
 * table, startup code and flash placement.
 */
SECTIONS
{
    . = 0x20000000;
    .text : { *(.text .text.*) }
}
