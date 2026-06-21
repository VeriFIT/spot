#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Copyright (C) by the Spot authors, see the AUTHORS file for details.
#
# This file is part of Spot, a model checking library.
#
# Spot is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# Spot is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

"""Setup script for local pip installation of Spot.

This setup.py bridges the Python packaging world with Spot's autotools
build system.  It overrides the build_py command to run::

    ./configure --prefix=<temp> && make -j$(nproc) && make install

from a source distribution that already contains the generated
'configure' script (as produced by 'make dist').  Users only need a
C++20 compiler, Python development headers, and make.

The installed layout mirrors a standard autotools install inside the
virtual environment::

    $VENV/
      bin/                         # native CLI tools (ltl2tgba, autfilt, ...)
      lib/                         # shared libraries (libspot.so, ...)
      lib/python3.X/site-packages/
        spot/                      # Python package + SWIG .so extensions
        _buddy*.so                 # BuDDy SWIG extension
        buddy.py

Rpaths are set so that CLI tools find shared libs via ``$ORIGIN/../lib``
and SWIG extensions find them via ``$ORIGIN/../../..`` (from
site-packages/spot/) or ``$ORIGIN/../..`` (from site-packages/).
"""

import os
import re
import sys
import shutil
import subprocess
from setuptools import setup
from setuptools.command.build_py import build_py as _build_py
from distutils.command.build_scripts import \
    build_scripts as _build_scripts


def get_version():
    """Extract the Spot version string from configure.ac."""
    here = os.path.dirname(os.path.abspath(__file__))
    configure_ac = os.path.join(here, 'configure.ac')
    with open(configure_ac) as f:
        content = f.read()
    m = re.search(r'AC_INIT\(\[spot\],\s*\[([^\]]+)\]', content)
    return m.group(1) if m else '0.0.0'


# ---------------------------------------------------------------------------
# Custom commands
# ---------------------------------------------------------------------------


class autotools_build_py(_build_py):
    """build_py subclass that delegates compilation to autotools."""

    def run(self):
        srcdir = os.getcwd()
        # build_base lives on the 'build' command, not 'build_py'
        build_cmd = self.get_finalized_command('build')
        build_base = build_cmd.build_base
        prefix = os.path.abspath(os.path.join(build_base, 'install'))
        builddir = os.path.abspath(os.path.join(build_base, 'autobuild'))
        os.makedirs(builddir, exist_ok=True)

        # -- configure -------------------------------------------------------
        configure = os.path.join(srcdir, 'configure')
        if not os.path.isfile(configure):
            sys.exit("No 'configure' found. Are you building from a release "
                     "tarball produced by 'make dist'?")

        subprocess.check_call([
            configure,
            '--disable-devel',
            '--enable-optimizations',
            '--prefix=' + prefix,
            'PYTHON=' + sys.executable,
        ], cwd=builddir)

        # -- build -----------------------------------------------------------
        nproc = str(os.cpu_count() or 1)
        subprocess.check_call(['make', '-j' + nproc], cwd=builddir)
        subprocess.check_call(['make', 'install'], cwd=builddir)

        # -- locate the installed Python tree --------------------------------
        pysrc = self._find_python_site(prefix)

        # -- copy Python files + SWIG .so files to build_lib -----------------
        self.mkpath(self.build_lib)
        for item in os.listdir(pysrc):
            src = os.path.join(pysrc, item)
            dst = os.path.join(self.build_lib, item)
            if os.path.isdir(src):
                if os.path.exists(dst):
                    shutil.rmtree(dst)
                shutil.copytree(src, dst, symlinks=True)
            else:
                shutil.copy2(src, dst, follow_symlinks=False)

        # -- register shared libraries as data_files → $VENV/lib/ -----------
        lib_files = []
        libdir = os.path.join(prefix, 'lib')
        for f in sorted(os.listdir(libdir)):
            if '.so' in f or '.dylib' in f:
                lib_files.append(os.path.join(libdir, f))
        self.distribution.data_files = [('lib', lib_files)]

        # -- register CLI tools as scripts → $VENV/bin/ -------------------
        bindir = os.path.join(prefix, 'bin')
        self.distribution.scripts = sorted(
            os.path.join(bindir, f)
            for f in os.listdir(bindir)
            if os.path.isfile(os.path.join(bindir, f))
            and os.access(os.path.join(bindir, f), os.X_OK)
        )

        # -- fix rpaths ------------------------------------------------------
        spot_pkg = os.path.join(self.build_lib, 'spot')
        self._fix_rpaths(spot_pkg, bindir)

        # -- update distribution metadata for correct wheel content ---------
        pkg_list = ['spot']
        for root, _dirs, files in os.walk(self.build_lib):
            rel = os.path.relpath(root, self.build_lib)
            if rel == '.':
                continue
            if '__init__.py' in files:
                pkg_list.append(rel.replace(os.sep, '.'))
        self.distribution.packages = pkg_list
        self.distribution.py_modules = ['buddy']

        # -- byte-compile the Python files -----------------------------------
        import compileall
        py_files = []
        for root, _dirs, files in os.walk(self.build_lib):
            for f in files:
                if f.endswith('.py'):
                    py_files.append(os.path.join(root, f))
        if py_files:
            compileall.compile_dir(self.build_lib, force=self.force,
                                   quiet=1)

    # -- helpers -------------------------------------------------------------

    def get_outputs(self):
        """Return every file we placed in build_lib (required for wheels)."""
        outputs = []
        for root, _dirs, files in os.walk(self.build_lib):
            for f in files:
                outputs.append(os.path.join(root, f))
        return outputs

    def _find_python_site(self, prefix):
        """Walk *prefix* and return the directory containing
        spot/__init__.py."""
        for root, dirs, _files in os.walk(prefix):
            if 'spot' in dirs:
                sp = os.path.join(root, 'spot')
                if os.path.isfile(os.path.join(sp, '__init__.py')):
                    return root
        raise RuntimeError(
            f"Cannot find installed 'spot' Python package under {prefix}"
        )

    # -- rpath helpers -------------------------------------------------------

    def _fix_rpaths(self, spot_pkg, cli_bindir):
        if sys.platform == 'darwin':
            self._fix_rpaths_macos(spot_pkg, cli_bindir)
        else:
            self._fix_rpaths_linux(spot_pkg, cli_bindir)

    def _find_rpath_tool(self, candidates):
        for name in candidates:
            try:
                subprocess.check_call([name, '--version'],
                                      stdout=subprocess.DEVNULL,
                                      stderr=subprocess.DEVNULL)
                return name
            except (FileNotFoundError, subprocess.CalledProcessError):
                pass
        return None

    def _fix_rpaths_linux(self, spot_pkg, cli_bindir):
        tool = self._find_rpath_tool(['patchelf', 'chrpath'])
        if tool is None:
            sys.exit(
                "Neither 'patchelf' nor 'chrpath' was found.  "
                "One of these tools is required to set correct rpaths "
                "in the installed extension modules.\n"
                "Install patchelf with your package manager, e.g.:\n"
                "  apt install patchelf     (Debian/Ubuntu)\n"
                "  dnf install patchelf     (Fedora)\n"
                "  pacman -S patchelf       (Arch)\n"
                "Then re-run 'pip install'."
            )

        # SWIG extensions and shared libs in the spot package
        #  rpath $ORIGIN/../../.. → $VENV/lib/
        for f in os.listdir(spot_pkg):
            path = os.path.join(spot_pkg, f)
            if f.endswith('.so') and not os.path.islink(path):
                self._set_rpath_linux(tool, path, '$ORIGIN/../../..')

        # _buddy*.so lives directly in site-packages/
        #  rpath $ORIGIN/../.. → $VENV/lib/
        for f in os.listdir(self.build_lib):
            path = os.path.join(self.build_lib, f)
            if (f.startswith('_buddy') and f.endswith('.so')
                    and not os.path.islink(path)):
                self._set_rpath_linux(tool, path, '$ORIGIN/../..')

        # CLI binaries  –  rpath $ORIGIN/../lib → $VENV/lib/
        for f in os.listdir(cli_bindir):
            path = os.path.join(cli_bindir, f)
            if os.path.isfile(path) and not os.path.islink(path):
                self._set_rpath_linux(tool, path, '$ORIGIN/../lib')

    def _set_rpath_linux(self, tool, path, rpath):
        if tool == 'patchelf':
            subprocess.check_call(['patchelf', '--set-rpath',
                                   rpath, path])
        else:
            subprocess.check_call(['chrpath', '-r', rpath, path])

    def _fix_rpaths_macos(self, spot_pkg, cli_bindir):
        tool = self._find_rpath_tool(['install_name_tool'])
        if tool is None:
            sys.exit(
                "'install_name_tool' was not found.  "
                "This tool is required to fix shared library paths "
                "in the installed extension modules.\n"
                "Install the Xcode command-line tools:\n"
                "  xcode-select --install\n"
                "Then re-run 'pip install'."
            )

        lib_files = self.distribution.data_files
        lib_names = set()
        if lib_files:
            for _dest, paths in lib_files:
                for p in paths:
                    lib_names.add(os.path.basename(p))

        for f in os.listdir(spot_pkg):
            path = os.path.join(spot_pkg, f)
            if (f.endswith('.so') or f.endswith('.dylib')) and \
               not os.path.islink(path):
                self._fix_macho_deps(tool, path, lib_names)
                subprocess.check_call([tool, '-add_rpath',
                                       '@loader_path/../../..', path],
                                      stderr=subprocess.DEVNULL)

        for f in os.listdir(self.build_lib):
            path = os.path.join(self.build_lib, f)
            if (f.startswith('_buddy') and f.endswith('.so')
                    and not os.path.islink(path)):
                self._fix_macho_deps(tool, path, lib_names)
                subprocess.check_call([tool, '-add_rpath',
                                       '@loader_path/../..', path],
                                      stderr=subprocess.DEVNULL)

        for f in os.listdir(cli_bindir):
            path = os.path.join(cli_bindir, f)
            if os.path.isfile(path) and not os.path.islink(path):
                self._fix_macho_deps(tool, path, lib_names)
                subprocess.check_call([tool, '-add_rpath',
                                       '@loader_path/../lib', path],
                                      stderr=subprocess.DEVNULL)

    def _fix_macho_deps(self, tool, path, lib_names):
        """Rewrite Mach-O dependencies from absolute build paths to
        @rpath/<libname>."""
        try:
            out = subprocess.check_output(
                ['otool', '-L', path],
                text=True, stderr=subprocess.DEVNULL)
        except (FileNotFoundError, subprocess.CalledProcessError):
            return
        for line in out.splitlines():
            line = line.strip()
            for lib in lib_names:
                if lib in line and line.startswith('/'):
                    old_path = line.split()[0]
                    subprocess.check_call(
                        [tool, '-change', old_path,
                         '@rpath/' + lib, path],
                        stderr=subprocess.DEVNULL)


class autotools_build_scripts(_build_scripts):
    """Copy native CLI binaries into $VENV/bin/ without trying to
    parse them as text (which the default copy_scripts() does)."""

    def run(self):
        if not self.scripts:
            return
        self.mkpath(self.build_dir)
        self._copied = []
        for script in self.scripts:
            outfile = os.path.join(self.build_dir,
                                   os.path.basename(script))
            self.copy_file(script, outfile)
            self._copied.append(outfile)

    def get_outputs(self):
        return getattr(self, '_copied', [])


# ---------------------------------------------------------------------------
# Setup call
# ---------------------------------------------------------------------------
setup(
    name='spot',
    version=get_version(),
    packages=['spot'],
    py_modules=['buddy'],
    cmdclass={
        'build_py': autotools_build_py,
        'build_scripts': autotools_build_scripts,
    },
)
