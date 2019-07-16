# linux-install

Follow [this instruction](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries/Linux.html).

1. Download [tlaps-1.4.3-i686-linux-gnu-inst.bin](https://tla.msr-inria.inria.fr/tlaps/content/Download/Binaries/Linux.html)

2. `chmod a+x tlaps-1.4.3-i686-linux-gnu-inst.bin`

3. (Optional)
`tlaps-1.4.3-i686-linux-gnu-inst.bin` is for 32bit arch.
If your linux system is 64bit arch, do

- [sudo apt install libc6:i386](https://unix.stackexchange.com/questions/282422/cannot-run-32-bit-executable-on-64-bit-system-with-multi-arch-support)
Not sure whether this is necessary.

- [sudo dpkg --add-architecture i386](https://unix.stackexchange.com/questions/12956/how-do-i-run-32-bit-programs-on-a-64-bit-debian-ubuntu/47003#47003)

`tlaps-1.4.3-i686-linux-gnu-inst.bin` needs `libstdc++6`:
- [sudo apt install libstdc++6:i386](https://unix.stackexchange.com/questions/12956/how-do-i-run-32-bit-programs-on-a-64-bit-debian-ubuntu/47003#47003)

4. `sudo ./tlaps-1.4.3-i686-linux-gnu-inst.bin`

Install `tlaps` into `/usr/local`: `/usr/local/lib/tlaps/`

5. Set the toolbox's library path.

- Toolbox: `File > Preferences > TLA+ Preferences > Add Directory`.
- Add the directory where TLAPS.tla is located (`/usr/local/lib/tlaps`) to the list of library path locations.

6. Copy the example files

Copy `/usr/local/lib/tlaps/examples` to home directory.

7. Uninstall tlaps

- `tlapm --where`/un-inst
