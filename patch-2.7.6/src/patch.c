/* patch - a program to apply diffs to original files */

/* Copyright (C) 1984, 1985, 1986, 1987, 1988 Larry Wall

   Copyright (C) 1989-1993, 1997-1999, 2002-2003, 2006, 2009-2012 Free Software
   Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

#define XTERN
#include <common.h>
#undef XTERN
#define XTERN extern
#include <argmatch.h>
#include <exitfail.h>
#include <getopt.h>
#include <inp.h>
#include <pch.h>
#include <quotearg.h>
#include <util.h>
#include <version.h>
#include <xalloc.h>
#include <gl_linked_list.h>
#include <gl_xlist.h>
#include <minmax.h>
#include <safe.h>

#include "sha1.h"
#include "sha256.h"
#include "dirent.h"

#define GITOID_LENGTH_SHA1 20
#define GITOID_LENGTH_SHA256 32
#define MAX_FILE_SIZE_STRING_LENGTH 256

/* procedures */

static FILE *create_output_file (char const *, int);
static lin locate_hunk (lin);
static bool check_line_endings (lin);
static bool apply_hunk (struct outstate *, lin);
static bool patch_match (lin, lin, lin, lin);
static bool spew_output (struct outstate *, struct stat *);
static int numeric_string (char const *, bool, char const *);
static void cleanup (void);
static void get_some_switches (void);
static void init_output (struct outstate *);
static FILE *open_outfile (char const *);
static void init_reject (char const *);
static void reinitialize_almost_everything (void);
static void remove_if_needed (char const *, bool *);
static void usage (FILE *, int) __attribute__((noreturn));

static void abort_hunk (char const *, bool, bool);
static void abort_hunk_context (bool, bool);
static void abort_hunk_unified (bool, bool);

static void output_file (char const *, bool *, const struct stat *, char const *,
			 const struct stat *, mode_t, bool);

static void init_files_to_delete (void);
static void init_files_to_output (void);
static void init_omnibor_lines (void);
static void init_omnibor_files_to_add (void);
static void delete_files (void);
static void output_files (struct stat const *);
static void embed_omnibor_id (void);
static bool get_sha1 (const char *, unsigned char [2 * GITOID_LENGTH_SHA1 + 1]);
static bool get_sha256 (const char *,
			unsigned char [2 * GITOID_LENGTH_SHA256 + 1]);
static bool omnibor_add_file (const char *);
static void gl_list_clear (gl_list_t);

#ifdef ENABLE_MERGE
static bool merge;
#else
# define merge false
#endif

static enum diff reject_format = NO_DIFF;  /* automatic */
static bool make_backups;
static bool backup_if_mismatch;
static char const *version_control;
static char const *version_control_context;
static bool remove_empty_files;
static bool explicit_inname;
static enum { RO_IGNORE, RO_WARN, RO_FAIL } read_only_behavior = RO_WARN;

/* true if -R was specified on command line.  */
static bool reverse_flag_specified;

static char const *do_defines; /* symbol to patch using ifdef, ifndef, etc. */
static char const if_defined[] = "\n#ifdef %s\n";
static char const not_defined[] = "\n#ifndef %s\n";
static char const else_defined[] = "\n#else\n";
static char const end_defined[] = "\n#endif\n";

static int Argc;
static char **Argv;

static FILE *rejfp;  /* reject file pointer */

static char const *patchname;
static char *rejname;
static char const * TMPREJNAME;
static bool TMPREJNAME_needs_removal;

static lin maxfuzz = 2;

static char serrbuf[BUFSIZ];

static char *omnibor_dir;
static char *omnibor_option_arg;

/* Apply a set of diffs as appropriate. */

int
main (int argc, char **argv)
{
    char const *val;
    bool somefailed = false;
    struct outstate outstate;
    struct stat tmpoutst;
    char numbuf[LINENUM_LENGTH_BOUND + 1];
    bool written_to_rejname = false;
    bool skip_reject_file = false;
    bool apply_empty_patch = false;
    mode_t file_type;
    int outfd = -1;
    bool have_git_diff = false;

    exit_failure = 2;
    set_program_name (argv[0]);
    init_time ();

    setbuf(stderr, serrbuf);

    bufsize = 8 * 1024;
    buf = xmalloc (bufsize);

    strippath = -1;

    val = getenv ("QUOTING_STYLE");
    {
      int i = val ? argmatch (val, quoting_style_args, 0, 0) : -1;
      set_quoting_style ((struct quoting_options *) 0,
			 i < 0 ? shell_quoting_style : (enum quoting_style) i);
    }

    posixly_correct = getenv ("POSIXLY_CORRECT") != 0;
    backup_if_mismatch = ! posixly_correct;
    patch_get = ((val = getenv ("PATCH_GET"))
		 ? numeric_string (val, true, "PATCH_GET value")
		 : 0);

    val = getenv ("SIMPLE_BACKUP_SUFFIX");
    simple_backup_suffix = val && *val ? val : ".orig";

    if ((version_control = getenv ("PATCH_VERSION_CONTROL")))
      version_control_context = "$PATCH_VERSION_CONTROL";
    else if ((version_control = getenv ("VERSION_CONTROL")))
      version_control_context = "$VERSION_CONTROL";

    init_backup_hash_table ();
    init_files_to_delete ();
    init_files_to_output ();
    init_omnibor_files_to_add ();

    /* parse switches */
    Argc = argc;
    Argv = argv;
    get_some_switches();

    /* Make get_date() assume that context diff headers use UTC. */
    if (set_utc)
      setenv ("TZ", "UTC", 1);

    if (make_backups | backup_if_mismatch)
      backup_type = get_version (version_control_context, version_control);

    init_output (&outstate);
    if (outfile)
      outstate.ofp = open_outfile (outfile);

    /* Make sure we clean up in case of disaster.  */
    set_signals (false);

    /* When the file to patch is specified on the command line, allow that file
       to lie outside the current working tree.  Still doesn't allow to follow
       symlinks.  */
    if (inname)
      unsafe = true;

    if (inname && outfile)
      {
	/* When an input and an output filename is given and the patch is
	   empty, copy the input file to the output file.  In this case, the
	   input file must be a regular file (i.e., symlinks cannot be copied
	   this way).  */
	apply_empty_patch = true;
	file_type = S_IFREG;
	inerrno = -1;
      }
    for (
	open_patch_file (patchname);
	there_is_another_patch (! (inname || posixly_correct), &file_type)
	  || apply_empty_patch;
	reinitialize_almost_everything(),
	  skip_reject_file = false,
	  apply_empty_patch = false
    ) {					/* for each patch in patch file */
      int hunk = 0;
      int failed = 0;
      bool mismatch = false;
      char const *outname = NULL;

      if (skip_rest_of_patch)
	somefailed = true;

      if (have_git_diff != pch_git_diff ())
	{
	  if (have_git_diff)
	    {
	      output_files (NULL);
	      inerrno = -1;
	    }
	  have_git_diff = ! have_git_diff;
	}

      if (TMPREJNAME_needs_removal)
	{
	  if (rejfp)
	    {
	      fclose (rejfp);
	      rejfp = NULL;
	    }
	  remove_if_needed (TMPREJNAME, &TMPREJNAME_needs_removal);
	}
      if (TMPOUTNAME_needs_removal)
        {
	  if (outfd != -1)
	    {
	      close (outfd);
	      outfd = -1;
	    }
	  remove_if_needed (TMPOUTNAME, &TMPOUTNAME_needs_removal);
	}

      if (! skip_rest_of_patch && ! file_type)
	{
	  say ("File %s: can't change file type from 0%o to 0%o.\n",
	       quotearg (inname),
	       (unsigned int) (pch_mode (reverse) & S_IFMT),
	       (unsigned int) (pch_mode (! reverse) & S_IFMT));
	  skip_rest_of_patch = true;
	  somefailed = true;
	}

      if (! skip_rest_of_patch)
	{
	  if (outfile)
	    outname = outfile;
	  else if (pch_copy () || pch_rename ())
	    outname = pch_name (! reverse);
	  else
	    outname = inname;
	}

      if (pch_git_diff () && ! skip_rest_of_patch)
	{
	  struct stat outstat;
	  int outerrno = 0;

	  /* Try to recognize concatenated git diffs based on the SHA1 hashes
	     in the headers.  Will not always succeed for patches that rename
	     or copy files.  */

	  if (! strcmp (inname, outname))
	    {
	      if (inerrno == -1)
		inerrno = stat_file (inname, &instat);
	      outstat = instat;
	      outerrno = inerrno;
	    }
	  else
	    outerrno = stat_file (outname, &outstat);

	  if (! outerrno)
	    {
	      if (has_queued_output (&outstat))
		{
		  output_files (&outstat);
		  outerrno = stat_file (outname, &outstat);
		  inerrno = -1;
		}
	      if (! outerrno)
		set_queued_output (&outstat, true);
	    }
	}

      if (! skip_rest_of_patch)
	{
	  if (! get_input_file (inname, outname, file_type))
	    {
	      skip_rest_of_patch = true;
	      somefailed = true;
	    }
	}

      if (read_only_behavior != RO_IGNORE
	  && ! inerrno && ! S_ISLNK (instat.st_mode)
	  && safe_access (inname, W_OK) != 0)
	{
	  say ("File %s is read-only; ", quotearg (inname));
	  if (read_only_behavior == RO_WARN)
	    say ("trying to patch anyway\n");
	  else
	    {
	      say ("refusing to patch\n");
	      skip_rest_of_patch = true;
	      somefailed = true;
	    }
	}

      tmpoutst.st_size = -1;
      outfd = make_tempfile (&TMPOUTNAME, 'o', outname,
			     O_WRONLY | binary_transput,
			     instat.st_mode & S_IRWXUGO);
      if (outfd == -1)
	{
	  if (errno == ELOOP || errno == EXDEV)
	    {
	      say ("Invalid file name %s -- skipping patch\n", quotearg (outname));
	      skip_rest_of_patch = true;
	      skip_reject_file = true;
	      somefailed = true;
	    }
	  else
	    pfatal ("Can't create temporary file %s", TMPOUTNAME);
	}
      else
        TMPOUTNAME_needs_removal = true;
      if (diff_type == ED_DIFF) {
	outstate.zero_output = false;
	somefailed |= skip_rest_of_patch;
	do_ed_script (inname, TMPOUTNAME, &TMPOUTNAME_needs_removal,
		      outstate.ofp);
	if (! dry_run && ! outfile && ! skip_rest_of_patch)
	  {
	    if (fstat (outfd, &tmpoutst) != 0)
	      pfatal ("%s", TMPOUTNAME);
	    outstate.zero_output = tmpoutst.st_size == 0;
	  }
	close (outfd);
	outfd = -1;
      } else {
	int got_hunk;
	bool apply_anyway = merge;  /* don't try to reverse when merging */

	if (! skip_rest_of_patch && diff_type == GIT_BINARY_DIFF) {
	  say ("File %s: git binary diffs are not supported.\n",
	       quotearg (outname));
	  skip_rest_of_patch = true;
	  somefailed = true;
	}
	/* initialize the patched file */
	if (! skip_rest_of_patch && ! outfile)
	  {
	    init_output (&outstate);
	    outstate.ofp = fdopen(outfd, binary_transput ? "wb" : "w");
	    if (! outstate.ofp)
	      pfatal ("%s", TMPOUTNAME);
	    /* outstate.ofp now owns the file descriptor */
	    outfd = -1;
	  }

	/* find out where all the lines are */
	if (!skip_rest_of_patch) {
	    scan_input (inname, file_type);

	    if (verbosity != SILENT)
	      {
		bool renamed = strcmp (inname, outname);
		bool skip_rename = ! renamed && pch_rename ();

		say ("%s %s %s%c",
		     dry_run ? "checking" : "patching",
		     S_ISLNK (file_type) ? "symbolic link" : "file",
		     quotearg (outname), renamed || skip_rename ? ' ' : '\n');
                omnibor_add_file (outname);
                if (renamed || skip_rename)
		  say ("(%s%s from %s)\n",
		       skip_rename ? "already " : "",
		       pch_copy () ? "copied" :
		       (pch_rename () ? "renamed" : "read"),
		       ! skip_rename ? inname : pch_name (! strcmp (inname, pch_name (OLD))));
		if (verbosity == VERBOSE)
		  say ("Using Plan %s...\n", using_plan_a ? "A" : "B");
	      }
	}

	/* from here on, open no standard i/o files, because malloc */
	/* might misfire and we can't catch it easily */

	/* apply each hunk of patch */
	while (0 < (got_hunk = another_hunk (diff_type, reverse)))
	  {
	    lin where = 0; /* Pacify 'gcc -Wall'.  */
	    lin newwhere;
	    lin fuzz = 0;
	    lin mymaxfuzz;

	    if (merge)
	      {
		/* When in merge mode, don't apply with fuzz.  */
		mymaxfuzz = 0;
	      }
	    else
	      {
		lin prefix_context = pch_prefix_context ();
		lin suffix_context = pch_suffix_context ();
		lin context = (prefix_context < suffix_context
			       ? suffix_context : prefix_context);
		mymaxfuzz = (maxfuzz < context ? maxfuzz : context);
	      }

	    hunk++;
	    if (!skip_rest_of_patch) {
		do {
		    where = locate_hunk(fuzz);
		    if (! where || fuzz || in_offset)
		      mismatch = true;
		    if (hunk == 1 && ! where && ! (force | apply_anyway)
			&& reverse == reverse_flag_specified) {
						/* dwim for reversed patch? */
			if (!pch_swap()) {
			    say (
"Not enough memory to try swapped hunk!  Assuming unswapped.\n");
			    continue;
			}
			/* Try again.  */
			where = locate_hunk (fuzz);
			if (where
			    && (ok_to_reverse
				("%s patch detected!",
				 (reverse
				  ? "Unreversed"
				  : "Reversed (or previously applied)"))))
			  reverse = ! reverse;
			else
			  {
			    /* Put it back to normal.  */
			    if (! pch_swap ())
			      fatal ("lost hunk on alloc error!");
			    if (where)
			      {
				apply_anyway = true;
				fuzz--; /* Undo '++fuzz' below.  */
				where = 0;
			      }
			  }
		    }
		} while (!skip_rest_of_patch && !where
			 && ++fuzz <= mymaxfuzz);

		if (skip_rest_of_patch) {		/* just got decided */
		  if (outstate.ofp && ! outfile)
		    {
		      fclose (outstate.ofp);
		      outstate.ofp = 0;
		      outfd = -1;
		    }
		}
	    }

	    newwhere = (where ? where : pch_first()) + out_offset;
	    if (skip_rest_of_patch
		|| (merge && ! merge_hunk (hunk, &outstate, where,
					   &somefailed))
		|| (! merge
		    && ((where == 1 && pch_says_nonexistent (reverse) == 2
			 && instat.st_size)
			|| ! where
			|| ! apply_hunk (&outstate, where))))
	      {
		if (! skip_reject_file)
		  abort_hunk (outname, ! failed, reverse);
		failed++;
		if (verbosity == VERBOSE ||
		    (! skip_rest_of_patch && verbosity != SILENT))
		  say ("Hunk #%d %s at %s%s.\n", hunk,
		       skip_rest_of_patch ? "ignored" : "FAILED",
		       format_linenum (numbuf, newwhere),
		       ! skip_rest_of_patch && check_line_endings (newwhere)
			 ?  " (different line endings)" : "");
	      }
	    else if (! merge &&
		     (verbosity == VERBOSE
		      || (verbosity != SILENT && (fuzz || in_offset))))
	      {
		say ("Hunk #%d succeeded at %s", hunk,
		     format_linenum (numbuf, newwhere));
		if (fuzz)
		  say (" with fuzz %s", format_linenum (numbuf, fuzz));
		if (in_offset)
		  say (" (offset %s line%s)",
		       format_linenum (numbuf, in_offset),
		       "s" + (in_offset == 1));
		say (".\n");
	      }
	  }

	if (!skip_rest_of_patch)
	  {
	    if (got_hunk < 0  &&  using_plan_a)
	      {
		if (outfile)
		  fatal ("out of memory using Plan A");
		say ("\n\nRan out of memory using Plan A -- trying again...\n\n");
		if (outstate.ofp)
		  {
		    fclose (outstate.ofp);
		    outstate.ofp = 0;
		  }
		continue;
	      }

	    /* Finish spewing out the new file.  */
	    if (! spew_output (&outstate, &tmpoutst))
	      {
		say ("Skipping patch.\n");
		skip_rest_of_patch = true;
	      }
	  }
      }

      /* and put the output where desired */
      ignore_signals ();
      if (! skip_rest_of_patch && ! outfile) {
	  bool backup = make_backups
			|| (backup_if_mismatch && (mismatch | failed));
	  if (outstate.zero_output
	      && (remove_empty_files
		  || (pch_says_nonexistent (! reverse) == 2
		      && ! posixly_correct)
		  || S_ISLNK (file_type)))
	    {
	      if (! dry_run)
		output_file (NULL, NULL, NULL, outname,
			     (inname == outname) ? &instat : NULL,
			     file_type | 0, backup);
	    }
	  else
	    {
	      if (! outstate.zero_output
		  && pch_says_nonexistent (! reverse) == 2
		  && (remove_empty_files || ! posixly_correct)
		  && ! (merge && somefailed))
		{
		  mismatch = true;
		  somefailed = true;
		  if (verbosity != SILENT)
		    say ("Not deleting file %s as content differs from patch\n",
			 quotearg (outname));
		}

	      if (! dry_run)
		{
		  mode_t old_mode = pch_mode (reverse);
		  mode_t new_mode = pch_mode (! reverse);
		  bool set_mode = new_mode && old_mode != new_mode;

		  /* Avoid replacing files when nothing has changed.  */
		  if (failed < hunk || diff_type == ED_DIFF || set_mode
		      || pch_copy () || pch_rename ())
		    {
		      enum file_attributes attr = 0;
		      struct timespec new_time = pch_timestamp (! reverse);
		      mode_t mode = file_type |
			  ((set_mode ? new_mode : instat.st_mode) & S_IRWXUGO);

		      if ((set_time | set_utc) && new_time.tv_sec != -1)
			{
			  struct timespec old_time = pch_timestamp (reverse);

			  if (! force && ! inerrno
			      && pch_says_nonexistent (reverse) != 2
			      && old_time.tv_sec != -1
			      && timespec_cmp (old_time,
					       get_stat_mtime (&instat)))
			    say ("Not setting time of file %s "
				 "(time mismatch)\n",
				 quotearg (outname));
			  else if (! force && (mismatch | failed))
			    say ("Not setting time of file %s "
				 "(contents mismatch)\n",
				 quotearg (outname));
			  else
			    attr |= FA_TIMES;
			}

		      if (inerrno)
		        {
			  if (set_mode)
			    attr |= FA_MODE;
			  set_file_attributes (TMPOUTNAME, attr, NULL, NULL,
					       mode, &new_time);
			}
		      else
			{
			  attr |= FA_IDS | FA_MODE | FA_XATTRS;
			  set_file_attributes (TMPOUTNAME, attr, inname, &instat,
					       mode, &new_time);
			}

		      output_file (TMPOUTNAME, &TMPOUTNAME_needs_removal,
				   &tmpoutst, outname, NULL, mode, backup);

		      if (pch_rename ())
			output_file (NULL, NULL, NULL, inname, &instat,
				     mode, backup);
		    }
		  else
		    output_file (outname, NULL, &tmpoutst, NULL, NULL,
				 file_type | 0, backup);
		}
	    }
      }
      if (diff_type != ED_DIFF) {
	struct stat rejst;

	if (failed && ! skip_reject_file) {
	    if (fstat (fileno (rejfp), &rejst) != 0 || fclose (rejfp) != 0)
	      write_fatal ();
	    rejfp = NULL;
	    somefailed = true;
	    say ("%d out of %d hunk%s %s", failed, hunk, "s" + (hunk == 1),
		 skip_rest_of_patch ? "ignored" : "FAILED");
	    if (outname && (! rejname || strcmp (rejname, "-") != 0)) {
		char *rej = rejname;
		if (!rejname) {
		    /* FIXME: This should really be done differently!  */
		    const char *s = simple_backup_suffix;
		    size_t len;
		    simple_backup_suffix = ".rej";
		    rej = find_backup_file_name (outname, simple_backups);
		    len = strlen (rej);
		    if (rej[len - 1] == '~')
		      rej[len - 1] = '#';
		    simple_backup_suffix = s;
		}
		if (! dry_run)
		  {
		    say (" -- saving rejects to file %s\n", quotearg (rej));
		    if (rejname)
		      {
			if (! written_to_rejname)
			  {
			    copy_file (TMPREJNAME, rejname, 0, 0,
				       S_IFREG | 0666, true);
			    written_to_rejname = true;
			  }
			else
			  append_to_file (TMPREJNAME, rejname);
		      }
		    else
		      {
			struct stat oldst;
			int olderrno;

			olderrno = stat_file (rej, &oldst);
			if (olderrno && olderrno != ENOENT)
			  write_fatal ();
		        if (! olderrno && lookup_file_id (&oldst) == CREATED)
			  append_to_file (TMPREJNAME, rej);
			else
			  move_file (TMPREJNAME, &TMPREJNAME_needs_removal,
				     &rejst, rej, S_IFREG | 0666, false);
		      }
		  }
		else
		  say ("\n");
		if (!rejname)
		    free (rej);
	    } else
	      say ("\n");
	}
      }
      set_signals (true);
    }
    if (outstate.ofp && (ferror (outstate.ofp) || fclose (outstate.ofp) != 0))
      write_fatal ();
    output_files (NULL);
    cleanup ();
    delete_files ();
    if (somefailed)
      exit (1);

    if (omnibor_flag ||
       (getenv ("OMNIBOR_DIR") != NULL && strlen (getenv ("OMNIBOR_DIR")) > 0))
      embed_omnibor_id ();

    return 0;
}

/* OmniBOR list which contains pointers to the objects of the directories from
   the path to the directory where the OmniBOR information is to be stored. */

static gl_list_t omnibor_dirs;

static void
dispose_omnibor_dirs (const void *elt)
{
  const DIR *omnibor_dir = elt;

  closedir ((DIR *) omnibor_dir);
}

static void
init_omnibor_dirs (void)
{
  omnibor_dirs =
	gl_list_create_empty (GL_LINKED_LIST, NULL, NULL,
			      dispose_omnibor_dirs, false);
}

static void
omnibor_add_to_dirs (DIR **directory)
{
  gl_list_add_last (omnibor_dirs, *directory);
}

/* Return the position of the first occurrence after start_pos position
   of char c in str string (start_pos is the first position to check). */

static int
omnibor_find_char_from_pos (unsigned start_pos, char c, const char *str)
{
  for (unsigned ix = start_pos; ix < strlen (str); ix++)
    if (str[ix] == c)
      return ix;

  return -1;
}

/* Return the position of the last occurrence of char c in the entire
   str string. */

static int
omnibor_find_last_of (char c, const char *str)
{
  int ret = -1;
  for (unsigned ix = 0; ix < strlen (str); ix++)
    if (str[ix] == c)
      ret = ix;

  return ret;
}

/* Append the string str2 to the end of the string str1. */

static void
omnibor_append_to_string (char **str1, const char *str2,
			 unsigned long len1, unsigned long len2)
{
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len1 + len2 + 1));
  memcpy (*str1 + len1, str2, len2);
  (*str1)[len1 + len2] = '\0';
}

/* Get the substring of length len of the str2 string starting from
   the start position and put it in the str1 string. */

static void
omnibor_substr (char **str1, unsigned start, unsigned len, const char *str2)
{
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len + 1));
  memcpy (*str1, str2 + start, len);
  (*str1)[len] = '\0';
}

/* Set the string str1 to have the contents of the string str2. */

static void
omnibor_set_contents (char **str1, const char *str2, unsigned long len)
{
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len + 1));
  memcpy (*str1, str2, len);
  (*str1)[len] = '\0';
}

/* Add the string str2 as a prefix to the string str1. */

static void
omnibor_add_prefix_to_string (char **str1, const char *str2)
{
  unsigned len1 = strlen (*str1), len2 = strlen (str2);
  char *temp = (char *) xcalloc
	(len1 + len2 + 1, sizeof (char));
  memcpy (temp, str2, len2);
  memcpy (temp + len2, *str1, len1);
  temp[len1 + len2] = '\0';
  *str1 = (char *) xrealloc
	(*str1, sizeof (char) * (len1 + len2 + 1));
  memcpy (*str1, temp, len1 + len2);
  (*str1)[len1 + len2] = '\0';
  free (temp);
}

/* Calculate the SHA1 gitoid using the contents of the given file. */

static void
calculate_sha1_omnibor (FILE *dep_file, unsigned char resblock[])
{
  fseek (dep_file, 0L, SEEK_END);
  long file_size = ftell (dep_file);
  fseek (dep_file, 0L, SEEK_SET);

  /* This length should be enough for everything up to 64B, which should
     cover long type. */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  char *file_contents = (char *) xcalloc (file_size, sizeof (char));
  fread (file_contents, 1, file_size, dep_file);

  /* Calculate the hash. */
  struct sha1_ctx ctx;

  sha1_init_ctx (&ctx);

  sha1_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha1_process_bytes (file_contents, file_size, &ctx);

  sha1_finish_ctx (&ctx, resblock);

  free (file_contents);
  free (init_data);
}

/* Calculate the SHA1 gitoid using the given contents. */

void
calculate_sha1_omnibor_with_contents (char *contents,
				      unsigned char resblock[])
{
  long file_size = strlen (contents);

  /* This length should be enough for everything up to 64B, which should
     cover long type. */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  /* Calculate the hash. */
  struct sha1_ctx ctx;

  sha1_init_ctx (&ctx);

  sha1_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha1_process_bytes (contents, file_size, &ctx);

  sha1_finish_ctx (&ctx, resblock);

  free (init_data);
}

/* Calculate the SHA256 gitoid using the contents of the given file. */

void
calculate_sha256_omnibor (FILE *dep_file, unsigned char resblock[])
{
  fseek (dep_file, 0L, SEEK_END);
  long file_size = ftell (dep_file);
  fseek (dep_file, 0L, SEEK_SET);

  /* This length should be enough for everything up to 64B, which should
     cover long type. */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  char *file_contents = (char *) xcalloc (file_size, sizeof (char));
  fread (file_contents, 1, file_size, dep_file);

  /* Calculate the hash. */
  struct sha256_ctx ctx;

  sha256_init_ctx (&ctx);

  sha256_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha256_process_bytes (file_contents, file_size, &ctx);

  sha256_finish_ctx (&ctx, resblock);

  free (file_contents);
  free (init_data);
}

/* Calculate the SHA256 gitoid using the given contents. */

void
calculate_sha256_omnibor_with_contents (char *contents,
					unsigned char resblock[])
{
  long file_size = strlen (contents);

  /* This length should be enough for everything up to 64B, which should
     cover long type. */
  char buff_for_file_size[MAX_FILE_SIZE_STRING_LENGTH];
  sprintf (buff_for_file_size, "%ld", file_size);

  char *init_data = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&init_data, "blob ", strlen (init_data),
			    strlen ("blob "));
  omnibor_append_to_string (&init_data, buff_for_file_size, strlen (init_data),
			    strlen (buff_for_file_size));
  omnibor_append_to_string (&init_data, "\0", strlen (init_data), 1);

  /* Calculate the hash. */
  struct sha256_ctx ctx;

  sha256_init_ctx (&ctx);

  sha256_process_bytes (init_data, strlen (init_data) + 1, &ctx);
  sha256_process_bytes (contents, file_size, &ctx);

  sha256_finish_ctx (&ctx, resblock);

  free (init_data);
}

/* Get the SHA1 OmniBOR gitoid of the file with the given name. */

static bool
get_sha1 (const char *filename, unsigned char sha1[2 * GITOID_LENGTH_SHA1 + 1])
{
  static const char *const lut = "0123456789abcdef";
  FILE *fp;

  fp = fopen (filename, "r");

  unsigned char sha1_hash[GITOID_LENGTH_SHA1];
  calculate_sha1_omnibor (fp, sha1_hash);
  for (unsigned i = 0; i != GITOID_LENGTH_SHA1; ++i)
    {
      sha1[2 * i] = lut[sha1_hash[i] >> 4];
      sha1[2 * i + 1] = lut[sha1_hash[i] & 15];
    }
  sha1[2 * GITOID_LENGTH_SHA1] = '\0';

  /* Close FILE pointer. */
  fclose (fp);

  return 0;
}

/* Get the SHA256 OmniBOR gitoid of the file with the given name. */

static bool
get_sha256 (const char *filename,
	    unsigned char sha256[2 * GITOID_LENGTH_SHA256 + 1])
{
  static const char *const lut = "0123456789abcdef";
  FILE *fp;

  fp = fopen (filename, "r");

  unsigned char sha256_hash[GITOID_LENGTH_SHA256];
  calculate_sha256_omnibor (fp, sha256_hash);
  for (unsigned i = 0; i != GITOID_LENGTH_SHA256; ++i)
    {
      sha256[2 * i] = lut[sha256_hash[i] >> 4];
      sha256[2 * i + 1] = lut[sha256_hash[i] & 15];
    }
  sha256[2 * GITOID_LENGTH_SHA256] = '\0';

  /* Close FILE pointer. */
  fclose (fp);

  return 0;
}

/* OmniBOR dependency file struct. */

struct omnibor_file_to_add {
  /* Name of the file. */
  char *filename;

  /* SHA1 gitoid of the file. */
  unsigned char sha1[2 * GITOID_LENGTH_SHA1 + 1];

  /* SHA256 gitoid of the file. */
  unsigned char sha256[2 * GITOID_LENGTH_SHA256 + 1];
};

static gl_list_t omnibor_files_to_add;

static void
dispose_omnibor_files_to_add (const void *elt)
{
  const struct omnibor_file_to_add *omnibor_file_to_add = elt;

  free (omnibor_file_to_add->filename);
}

static void
init_omnibor_files_to_add (void)
{
  omnibor_files_to_add =
	gl_list_create_empty (GL_LINKED_LIST, NULL, NULL,
			      dispose_omnibor_files_to_add, false);
}

static bool
omnibor_add_file (const char *filename)
{
  struct omnibor_file_to_add *entry;

  if (!filename)
    return false;

  /* Check if filename is already in the list. */
  gl_list_iterator_t iter;
  const void *elt;

  iter = gl_list_iterator (omnibor_files_to_add);
  while (gl_list_iterator_next (&iter, &elt, NULL))
    {
      const struct omnibor_file_to_add *omnibor_file_to_add = elt;

      if (omnibor_file_to_add->filename == NULL)
	continue;
      if (strcmp (omnibor_file_to_add->filename, filename) == 0)
	return false;
    }

  entry = xmalloc (sizeof *entry);
  entry->filename = xstrdup (filename);
  get_sha1 (entry->filename, entry->sha1);
  get_sha256 (entry->filename, entry->sha256);

  gl_list_add_last (omnibor_files_to_add, entry);

  return true;
}

static gl_list_t omnibor_lines_sha1, omnibor_lines_sha256;

static void
dispose_omnibor_lines (const void *elt)
{
  const char *omnibor_line = elt;

  free ((char *) omnibor_line);
}

static void
init_omnibor_lines (void)
{
  omnibor_lines_sha1 =
	gl_list_create_empty (GL_LINKED_LIST, NULL, NULL,
			      dispose_omnibor_lines, false);
  omnibor_lines_sha256 =
	gl_list_create_empty (GL_LINKED_LIST, NULL, NULL,
			      dispose_omnibor_lines, false);
}

static int
omnibor_sort_sha1 (const void *elt1, const void *elt2)
{
  const char *line1 = elt1, *line2 = elt2;

  return memcmp (line1, line2, strlen ("blob ") + 2 * GITOID_LENGTH_SHA1);
}

static int
omnibor_sort_sha256 (const void *elt1, const void *elt2)
{
  const char *line1 = elt1, *line2 = elt2;

  return memcmp (line1, line2, strlen ("blob ") + 2 * GITOID_LENGTH_SHA256);
}

static void
omnibor_add_line (const unsigned char sha1[2 * GITOID_LENGTH_SHA1 + 1],
		  const unsigned char sha256[2 * GITOID_LENGTH_SHA256 + 1])
{
  char *omnibor_line_sha1, *omnibor_line_sha256;

  omnibor_line_sha1 = xcalloc (1, sizeof (char));
  omnibor_append_to_string (&omnibor_line_sha1, "blob ",
			    strlen (omnibor_line_sha1), strlen ("blob "));
  omnibor_append_to_string (&omnibor_line_sha1, sha1,
			    strlen (omnibor_line_sha1),
			    2 * GITOID_LENGTH_SHA1);
  omnibor_line_sha256 = xcalloc (1, sizeof (char));
  omnibor_append_to_string (&omnibor_line_sha256, "blob ",
			    strlen (omnibor_line_sha256), strlen ("blob "));
  omnibor_append_to_string (&omnibor_line_sha256, sha256,
			    strlen (omnibor_line_sha256),
			    2 * GITOID_LENGTH_SHA256);

  gl_sortedlist_add (omnibor_lines_sha1, omnibor_sort_sha1, omnibor_line_sha1);
  gl_sortedlist_add (omnibor_lines_sha256, omnibor_sort_sha256,
		     omnibor_line_sha256);
}

/* Open all the directories from the path specified in the res_dir
   parameter and put them in the omnibor_dirs list. Also create
   the directories which do not already exist. */

static DIR *
open_all_directories_in_path (const char *res_dir)
{
  char *path = (char *) xcalloc (1, sizeof (char));
  char *dir_name = (char *) xcalloc (1, sizeof (char));

  int old_p = 0, p = omnibor_find_char_from_pos (0, '/', res_dir);
  int dfd, absolute = 0;
  DIR *dir = NULL;

  if (p == -1)
    {
      free (dir_name);
      free (path);
      return NULL;
    }
  /* If the res_dir is an absolute path. */
  else if (p == 0)
    {
      absolute = 1;
      omnibor_append_to_string (&path, "/", strlen (path), strlen ("/"));
      /* Opening a root directory because an absolute path is specified. */
      dir = opendir (path);
      dfd = dirfd (dir);

      omnibor_add_to_dirs (&dir);
      p = p + 1;
      old_p = p;

      /* Path is of format "/<dir>" where dir does not exist. This point can be
         reached only if <dir> could not be created in the root folder, so it is
         considered as an illegal path. */
      if ((p = omnibor_find_char_from_pos (p, '/', res_dir)) == -1)
        {
	  free (dir_name);
	  free (path);
	  return NULL;
	}

      /* Process sequences of adjacent occurrences of character '/'. */
      while (old_p == p)
        {
          p = p + 1;
          old_p = p;
          p = omnibor_find_char_from_pos (p, '/', res_dir);
        }

      if (p == -1)
        {
	  free (dir_name);
	  free (path);
	  return NULL;
	}
    }

  omnibor_substr (&dir_name, old_p, p - old_p, res_dir);
  omnibor_append_to_string (&path, dir_name, strlen (path), strlen (dir_name));

  if ((dir = opendir (path)) == NULL)
    {
      if (absolute)
        mkdirat (dfd, dir_name, S_IRWXU);
      else
        mkdir (dir_name, S_IRWXU);
      dir = opendir (path);
    }

  if (dir == NULL)
    {
      free (dir_name);
      free (path);
      return NULL;
    }

  dfd = dirfd (dir);

  omnibor_add_to_dirs (&dir);
  p = p + 1;
  old_p = p;

  while ((p = omnibor_find_char_from_pos (p, '/', res_dir)) != -1)
    {
      /* Process sequences of adjacent occurrences of character '/'. */
      while (old_p == p)
        {
          p = p + 1;
          old_p = p;
          p = omnibor_find_char_from_pos (p, '/', res_dir);
        }

      if (p == -1)
        break;

      omnibor_substr (&dir_name, old_p, p - old_p, res_dir);
      omnibor_append_to_string (&path, "/", strlen (path), strlen ("/"));
      omnibor_append_to_string (&path, dir_name, strlen (path),
				strlen (dir_name));

      if ((dir = opendir (path)) == NULL)
        {
          mkdirat (dfd, dir_name, S_IRWXU);
          dir = opendir (path);
        }

      if (dir == NULL)
        {
	  free (dir_name);
	  free (path);
	  return NULL;
	}

      dfd = dirfd (dir);

      omnibor_add_to_dirs (&dir);
      p = p + 1;
      old_p = p;
    }

  if ((unsigned) old_p < strlen (res_dir))
    {
      omnibor_substr (&dir_name, old_p, strlen (res_dir) - old_p, res_dir);
      omnibor_append_to_string (&path, "/", strlen (path), strlen ("/"));
      omnibor_append_to_string (&path, dir_name, strlen (path),
				strlen (dir_name));

      if ((dir = opendir (path)) == NULL)
        {
          mkdirat (dfd, dir_name, S_IRWXU);
          dir = opendir (path);
        }

      omnibor_add_to_dirs (&dir);
    }

  free (dir_name);
  free (path);
  return dir;
}

/* Close all the directories from the omnibor_dirs list. This function should
   be called after calling the function open_all_directories_in_path. */

static void
close_all_directories_in_path (void)
{
  gl_list_clear (omnibor_dirs);
}

/* Store the OmniBOR information in the specified directory whose path is
   written in the result_dir parameter. If result_dir is NULL or an empty
   string, the OmniBOR information is stored in the current working directory.
   The hash_size parameter has to be either GITOID_LENGTH_SHA1 (for the SHA1
   OmniBOR information) or GITOID_LENGTH_SHA256 (for the SHA256 OmniBOR
   information). If any error occurs during the creation of the OmniBOR
   Document file, name parameter is set to point to an empty string. */

static void
create_omnibor_document_file (char **name, const char *result_dir,
			      char *new_file_contents, unsigned int new_file_size,
			      unsigned int hash_size)
{
  if (hash_size != GITOID_LENGTH_SHA1 && hash_size != GITOID_LENGTH_SHA256)
    {
      omnibor_set_contents (name, "", 0);
      return;
    }

  init_omnibor_dirs ();

  char *path_objects = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&path_objects, "objects", strlen (path_objects),
			    strlen ("objects"));
  DIR *dir_one = NULL;

  if (result_dir)
    {
      if ((dir_one = opendir (result_dir)) == NULL)
        {
          mkdir (result_dir, S_IRWXU);
	  dir_one = opendir (result_dir);
	}

      if (dir_one != NULL)
        {
          omnibor_add_prefix_to_string (&path_objects, "/");
          omnibor_add_prefix_to_string (&path_objects, result_dir);
          int dfd1 = dirfd (dir_one);
          mkdirat (dfd1, "objects", S_IRWXU);
        }
      else if (strlen (result_dir) != 0)
        {
          DIR *final_dir = open_all_directories_in_path (result_dir);
          /* If an error occurred, illegal path is detected and the OmniBOR
             information is not written. */
          /* TODO: Maybe put a message here that a specified path, in which
	     the OmniBOR information should be stored, is illegal. */
	  /* TODO: In case of an error, if any directories were created,
	     remove them. */
          if (final_dir == NULL)
            {
              close_all_directories_in_path ();
              free (path_objects);
              omnibor_set_contents (name, "", 0);
              return;
            }
          else
            {
              omnibor_add_prefix_to_string (&path_objects, "/");
	      omnibor_add_prefix_to_string (&path_objects, result_dir);
              int dfd1 = dirfd (final_dir);
              mkdirat (dfd1, "objects", S_IRWXU);
            }
        }
      else
        mkdir ("objects", S_IRWXU);
    }
  /* Put the OmniBOR Document file in the current working directory. */
  else
    mkdir ("objects", S_IRWXU);

  DIR *dir_two = opendir (path_objects);
  if (dir_two == NULL)
    {
      close_all_directories_in_path ();
      if (result_dir && dir_one)
        closedir (dir_one);
      free (path_objects);
      omnibor_set_contents (name, "", 0);
      return;
    }

  int dfd2 = dirfd (dir_two);

  char *path_sha = NULL;
  DIR *dir_three = NULL;
  if (hash_size == GITOID_LENGTH_SHA1)
    {
      mkdirat (dfd2, "gitoid_blob_sha1", S_IRWXU);

      path_sha = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&path_sha, path_objects, strlen (path_sha),
				strlen (path_objects));
      omnibor_append_to_string (&path_sha, "/gitoid_blob_sha1",
				strlen (path_sha),
				strlen ("/gitoid_blob_sha1"));
      dir_three = opendir (path_sha);
      if (dir_three == NULL)
        {
          closedir (dir_two);
          close_all_directories_in_path ();
          if (result_dir && dir_one)
            closedir (dir_one);
          free (path_sha);
          free (path_objects);
          omnibor_set_contents (name, "", 0);
          return;
        }
    }
  else
    {
      mkdirat (dfd2, "gitoid_blob_sha256", S_IRWXU);

      path_sha = (char *) xcalloc (1, sizeof (char));
      omnibor_append_to_string (&path_sha, path_objects, strlen (path_sha),
				strlen (path_objects));
      omnibor_append_to_string (&path_sha, "/gitoid_blob_sha256",
				strlen (path_sha),
				strlen ("/gitoid_blob_sha256"));
      dir_three = opendir (path_sha);
      if (dir_three == NULL)
        {
          closedir (dir_two);
          close_all_directories_in_path ();
          if (result_dir && dir_one)
            closedir (dir_one);
          free (path_sha);
          free (path_objects);
          omnibor_set_contents (name, "", 0);
          return;
        }
    }

  int dfd3 = dirfd (dir_three);
  char *name_substr = (char *) xcalloc (1, sizeof (char));
  omnibor_substr (&name_substr, 0, 2, *name);
  mkdirat (dfd3, name_substr, S_IRWXU);

  char *path_dir = (char *) xcalloc (1, sizeof (char));
  omnibor_append_to_string (&path_dir, path_sha, strlen (path_dir),
			    strlen (path_sha));
  omnibor_append_to_string (&path_dir, "/", strlen (path_dir),
			    strlen ("/"));

  /* Save current length of path_dir before characters from hash are added to
     the path. This is done because the calculation of the length of the path
     from here moving forward is done manually by adding the length of the
     following parts of the path since hash can produce '\0' characters, so
     strlen is not good enough. */
  unsigned long path_dir_temp_len = strlen (path_dir);

  omnibor_append_to_string (&path_dir, name_substr, path_dir_temp_len, 2);
  DIR *dir_four = opendir (path_dir);
  if (dir_four == NULL)
    {
      closedir (dir_three);
      closedir (dir_two);
      close_all_directories_in_path ();
      if (result_dir && dir_one)
        closedir (dir_one);
      free (path_dir);
      free (name_substr);
      free (path_sha);
      free (path_objects);
      omnibor_set_contents (name, "", 0);
      return;
    }

  char *new_file_path = (char *) xcalloc (1, sizeof (char));
  omnibor_substr (&name_substr, 2, 2 * hash_size - 2, *name);
  omnibor_append_to_string (&new_file_path, path_dir, strlen (new_file_path),
			    path_dir_temp_len + 2);
  omnibor_append_to_string (&new_file_path, "/", path_dir_temp_len + 2,
			    strlen ("/"));
  omnibor_append_to_string (&new_file_path, name_substr,
			    path_dir_temp_len + 2 + strlen ("/"),
			    2 * hash_size - 2);

  FILE *new_file = fopen (new_file_path, "w");
  if (new_file != NULL)
    {
      fwrite (new_file_contents, sizeof (char), new_file_size, new_file);
      fclose (new_file);
    }
  else
    omnibor_set_contents (name, "", 0);

  closedir (dir_four);
  closedir (dir_three);
  closedir (dir_two);
  close_all_directories_in_path ();
  if (result_dir && dir_one)
    closedir (dir_one);
  free (new_file_path);
  free (path_dir);
  free (name_substr);
  free (path_sha);
  free (path_objects);
}

/* Scan for existing OmniBOR gitoid and remove it. */

static bool
remove_omnibor_gitoid (const char *filename,
		       unsigned char bom_sha1[2 * GITOID_LENGTH_SHA1 + 1],
		       unsigned char bom_sha256[2 * GITOID_LENGTH_SHA256 + 1])
{
  bool retval = false;
  FILE *fp = fopen (filename, "r+");
  if (fp == NULL)
    fatal ("unable to open file %s to scan for existing OmniBOR gitoids",
	   filename);

  const int sha1_comment_prefix_len = strlen ("//gitoid:blob:sha1:");
  const int sha256_comment_prefix_len = strlen (":gitoid:blob:sha256:");
  int full_sha256_comment_prefix_len = -1;
  size_t len = 0;
  char *line;
  ssize_t bytes_read = 0;
  ssize_t read;

  while ((read = getline (&line, &len, fp)) != -1)
    {
      /* TODO: Currently, both SHA1 and SHA256 gitoids have to be present in a
	 comment for it to be considered an OmniBOR comment. Maybe make it
	 best effort (whichever gitoid is present, extract it). */
      if (strncmp (line, "//gitoid:blob:sha1:",
		   sha1_comment_prefix_len) == 0)
	{
	  if (strncmp (line + sha1_comment_prefix_len + 2 * GITOID_LENGTH_SHA1,
		       ":gitoid:blob:sha256:",
		       sha256_comment_prefix_len) == 0)
	    full_sha256_comment_prefix_len =
		sha1_comment_prefix_len + 2 * GITOID_LENGTH_SHA1 +
		sha256_comment_prefix_len;
	  else if (strncmp (line + sha1_comment_prefix_len +
			    2 * GITOID_LENGTH_SHA1 + strlen (" bom ") +
			    2 * GITOID_LENGTH_SHA1,
			    ":gitoid:blob:sha256:",
			    sha256_comment_prefix_len) == 0)
	    full_sha256_comment_prefix_len =
		sha1_comment_prefix_len + 2 * GITOID_LENGTH_SHA1 +
		strlen (" bom ") + 2 * GITOID_LENGTH_SHA1 +
		sha256_comment_prefix_len;

	  if (full_sha256_comment_prefix_len == -1)
	    continue;

	  strncpy (bom_sha1, line + sha1_comment_prefix_len,
		   2 * GITOID_LENGTH_SHA1);
	  strncpy (bom_sha256, line + full_sha256_comment_prefix_len,
		   2 * GITOID_LENGTH_SHA256);

	  /* Replace the current gitoids with an empty line. */
	  fseek (fp, bytes_read, SEEK_SET);
	  char *omnibor_line = xmalloc (read * sizeof (char));
	  memset (omnibor_line, ' ', read * sizeof (char));
	  fwrite (omnibor_line, 1, read - 1, fp);

	  free (omnibor_line);
	  retval = true;
	  break;
	}
      bytes_read += read;
    }

  fclose (fp);
  return retval;
}

/* Get the path of the directory where the patch file will be stored,
   because the OmniBOR information should be stored there as well, in
   the default case (when OMNIBOR_DIR environment variable is not set
   and --omnibor=<arg> is not used, but --omnibor is used instead). */

static void
omnibor_get_destdir (char **res)
{
  char *temp = (char *) xcalloc (1, sizeof (char));

  int i = -1;

  if ((i = omnibor_find_last_of ('/', patchname)) != -1)
    {
      omnibor_substr (&temp, 0, i, patchname);
      omnibor_set_contents (res, temp, strlen (temp));
    }
  else
    omnibor_set_contents (res, "", 0);

  free (temp);
}

/* Determine the directory to store the OmniBOR files in this order of
   precedence:
	1. If OMNIBOR_DIR environment variable is set, use this location.
	2. Use the directory name passed with --omnibor option.
	3. Default is to write the OmniBOR files in the same directory as the
	   patch file. */

static void
set_omnibor_dir (void)
{
  if (omnibor_flag ||
     (getenv ("OMNIBOR_DIR") != NULL && strlen (getenv ("OMNIBOR_DIR")) > 0))
    {
      omnibor_dir = (char *) xcalloc (1, sizeof (char));

      const char *env_omnibor = getenv ("OMNIBOR_DIR");
      if (env_omnibor != NULL)
        omnibor_set_contents (&omnibor_dir, env_omnibor, strlen (env_omnibor));

      if (strlen (omnibor_dir) == 0)
        {
          if (strlen (omnibor_option_arg) > 0)
            omnibor_set_contents (&omnibor_dir, omnibor_option_arg,
				  strlen (omnibor_option_arg));
          else
            {
	      char *res = (char *) xcalloc (1, sizeof (char));

              omnibor_get_destdir (&res);
              if (strlen (res) > 0)
                omnibor_set_contents (&omnibor_dir, res, strlen (res));
              else
                omnibor_set_contents (&omnibor_dir, "", 0);

	      free (res);
            }
        }
    }
}

/* Form the contents of the OmniBOR Document file. The hash_size parameter
   has to be either GITOID_LENGTH_SHA1 (for the SHA1 OmniBOR Document file)
   or GITOID_LENGTH_SHA256 (for the SHA256 OmniBOR Document file). Otherwise,
   omnibor_doc_sha_contents parameter is set to an empty string. */

static void
form_omnibor_file_contents (char **omnibor_doc_sha_contents,
			    unsigned int *current_length,
			    const unsigned line_length, unsigned int hash_size)
{
  if (hash_size != GITOID_LENGTH_SHA1 && hash_size != GITOID_LENGTH_SHA256)
    {
      omnibor_set_contents (omnibor_doc_sha_contents, "", 0);
      return;
    }

  gl_list_iterator_t iter;
  const void *elt;

  if (hash_size == GITOID_LENGTH_SHA1)
    iter = gl_list_iterator (omnibor_lines_sha1);
  else
    iter = gl_list_iterator (omnibor_lines_sha256);

  while (gl_list_iterator_next (&iter, &elt, NULL))
    {
      const char *omnibor_line = elt;

      omnibor_append_to_string (omnibor_doc_sha_contents, omnibor_line,
				*current_length,
				line_length);
      *current_length += line_length;
      omnibor_append_to_string (omnibor_doc_sha_contents, "\n",
				*current_length,
				strlen ("\n"));
      *current_length += strlen ("\n");
    }

  gl_list_iterator_free (&iter);
}

/* Form the name of the OmniBOR Document file and place it in the name
   parameter. The hash_size parameter has to be either GITOID_LENGTH_SHA1
   (for the SHA1 OmniBOR Document file) or GITOID_LENGTH_SHA256 (for the
   SHA256 OmniBOR Document file). Otherwise, name parameter is set to an
   empty string. */

static void
form_omnibor_file_name (char **name, char *omnibor_doc_sha_contents,
			unsigned int hash_size)
{
  if (hash_size != GITOID_LENGTH_SHA1 && hash_size != GITOID_LENGTH_SHA256)
    {
      omnibor_set_contents (name, "", 0);
      return;
    }

  static const char *const lut = "0123456789abcdef";

  unsigned char sha_hash[hash_size];
  if (hash_size == GITOID_LENGTH_SHA1)
    calculate_sha1_omnibor_with_contents (omnibor_doc_sha_contents, sha_hash);
  else
    calculate_sha256_omnibor_with_contents (omnibor_doc_sha_contents, sha_hash);

  unsigned char omnibor_id_sha[2 * hash_size + 1];
  for (unsigned i = 0; i != hash_size; ++i)
    {
      omnibor_id_sha[2 * i] = lut[sha_hash[i] >> 4];
      omnibor_id_sha[2 * i + 1] = lut[sha_hash[i] & 15];
    }
  omnibor_id_sha[2 * hash_size] = '\0';

  omnibor_set_contents (name, omnibor_id_sha, 2 * hash_size);
}

/* Create the SHA1 and SHA256 OmniBOR Document files for the patching process.
   Also, embed their gitoids into the files that are being changed as comments. */

static void
embed_omnibor_id (void)
{
  init_omnibor_lines ();
  set_omnibor_dir ();

  gl_list_iterator_t iter0, iter1;
  const void *elt;

  /* Add lines in OmniBOR Document files for files that are being changed as
     dependencies. */
  iter0 = gl_list_iterator (omnibor_files_to_add);
  while (gl_list_iterator_next (&iter0, &elt, NULL))
    {
      const struct omnibor_file_to_add *omnibor_file_to_add = elt;

      if (omnibor_file_to_add->filename == NULL)
	continue;

      omnibor_add_line (omnibor_file_to_add->sha1, omnibor_file_to_add->sha256);
    }

  gl_list_iterator_free (&iter0);

  /* Add patch file as a dependency. */
  unsigned char patch_sha1[2 * GITOID_LENGTH_SHA1 + 1];
  unsigned char patch_sha256[2 * GITOID_LENGTH_SHA256 + 1];

  get_sha1 (patchname, patch_sha1);
  get_sha256 (patchname, patch_sha256);

  omnibor_add_line (patch_sha1, patch_sha256);

  char *omnibor_doc_sha1_contents = xcalloc (1, sizeof (char));
  char *omnibor_doc_sha256_contents = xcalloc (1, sizeof (char));
  unsigned current_length_sha1 = strlen (omnibor_doc_sha1_contents);
  unsigned current_length_sha256 = strlen (omnibor_doc_sha256_contents);
  const unsigned line_length_sha1 = strlen ("blob ") + 2 * GITOID_LENGTH_SHA1;
  const unsigned line_length_sha256 = strlen ("blob ") + 2 * GITOID_LENGTH_SHA256;

  omnibor_append_to_string (&omnibor_doc_sha1_contents, "gitoid:blob:sha1\n",
			    current_length_sha1, strlen ("gitoid:blob:sha1\n"));
  current_length_sha1 += strlen ("gitoid:blob:sha1\n");
  omnibor_append_to_string (&omnibor_doc_sha256_contents, "gitoid:blob:sha256\n",
			    current_length_sha256, strlen ("gitoid:blob:sha256\n"));
  current_length_sha256 += strlen ("gitoid:blob:sha256\n");

  form_omnibor_file_contents (&omnibor_doc_sha1_contents, &current_length_sha1,
			      line_length_sha1, GITOID_LENGTH_SHA1);

  form_omnibor_file_contents (&omnibor_doc_sha256_contents, &current_length_sha256,
			      line_length_sha256, GITOID_LENGTH_SHA256);

  char *name_sha1 = xcalloc (1, sizeof (char));
  form_omnibor_file_name (&name_sha1, omnibor_doc_sha1_contents,
			  GITOID_LENGTH_SHA1);

  char *name_sha256 = xcalloc (1, sizeof (char));
  form_omnibor_file_name (&name_sha256, omnibor_doc_sha256_contents,
			  GITOID_LENGTH_SHA256);

  if (strcmp ("", name_sha1) == 0 || strcmp ("", name_sha256) == 0)
    {
      free (name_sha256);
      free (name_sha1);
      free (omnibor_doc_sha256_contents);
      free (omnibor_doc_sha1_contents);
      free (omnibor_dir);
      gl_list_clear (omnibor_lines_sha256);
      gl_list_clear (omnibor_lines_sha1);
      gl_list_clear (omnibor_files_to_add);
      fatal ("error in creation of OmniBOR Document files");
    }

  create_omnibor_document_file (&name_sha1, omnibor_dir,
				omnibor_doc_sha1_contents,
				current_length_sha1, GITOID_LENGTH_SHA1);

  create_omnibor_document_file (&name_sha256, omnibor_dir,
				omnibor_doc_sha256_contents,
				current_length_sha256, GITOID_LENGTH_SHA256);
  if (strcmp ("", name_sha1) == 0 || strcmp ("", name_sha256) == 0)
    {
      free (name_sha256);
      free (name_sha1);
      free (omnibor_doc_sha256_contents);
      free (omnibor_doc_sha1_contents);
      free (omnibor_dir);
      gl_list_clear (omnibor_lines_sha256);
      gl_list_clear (omnibor_lines_sha1);
      gl_list_clear (omnibor_files_to_add);
      fatal ("error in creation of OmniBOR Document files");
    }

  unsigned char bom_omnibor_id_sha1[2 * GITOID_LENGTH_SHA1 + 1];
  unsigned char bom_omnibor_id_sha256[2 * GITOID_LENGTH_SHA256 + 1];

  /* Embed OmniBOR gitoid in files modified by patch tool. */
  iter1 = gl_list_iterator (omnibor_files_to_add);
  while (gl_list_iterator_next (&iter1, &elt, NULL))
    {
      const struct omnibor_file_to_add *omnibor_file_to_add = elt;

      bool is_removed = false;
      if (omnibor_file_to_add->filename == NULL)
	continue;

      is_removed = remove_omnibor_gitoid (omnibor_file_to_add->filename,
					  bom_omnibor_id_sha1,
					  bom_omnibor_id_sha256);

      FILE *fp = fopen (omnibor_file_to_add->filename, "a");
      if (fp == NULL)
	fatal ("unable to open file %s for writing so as to embed OmniBOR gitoid",
	       omnibor_file_to_add->filename);

      fprintf (fp, "\n//gitoid:blob:sha1:");
      fwrite (name_sha1, 1, 2 * GITOID_LENGTH_SHA1, fp);
      if (is_removed)
	{
	  fwrite (" bom ", 1, 5, fp);
	  fwrite (bom_omnibor_id_sha1, 1, 2 * GITOID_LENGTH_SHA1, fp);
	}
      fprintf (fp, ":gitoid:blob:sha256:");
      fwrite (name_sha256, 1, 2 * GITOID_LENGTH_SHA256, fp);
      if (is_removed)
	{
	  fwrite (" bom ", 1, 5, fp);
	  fwrite (bom_omnibor_id_sha256, 1, 2 * GITOID_LENGTH_SHA256, fp);
	}
      fwrite ("\n", 1, 1, fp);

      fclose (fp);
    }

  gl_list_iterator_free (&iter1);

  free (name_sha256);
  free (name_sha1);
  free (omnibor_doc_sha256_contents);
  free (omnibor_doc_sha1_contents);
  free (omnibor_dir);

  gl_list_clear (omnibor_lines_sha256);
  gl_list_clear (omnibor_lines_sha1);
  gl_list_clear (omnibor_files_to_add);
}

/* Prepare to find the next patch to do in the patch file. */

static void
reinitialize_almost_everything (void)
{
    re_patch();
    re_input();

    input_lines = 0;
    last_frozen_line = 0;

    if (inname && ! explicit_inname) {
	free (inname);
	inname = 0;
    }

    in_offset = 0;
    out_offset = 0;

    diff_type = NO_DIFF;

    if (revision) {
	free(revision);
	revision = 0;
    }

    reverse = reverse_flag_specified;
    skip_rest_of_patch = false;
}

static char const shortopts[] = "bB:cd:D:eEfF:g:i:l"
#if 0 && defined ENABLE_MERGE
				"m"
#endif
				"nNo:p:r:RstTuvV:x:Y:z:Z";

static struct option const longopts[] =
{
  {"backup", no_argument, NULL, 'b'},
  {"prefix", required_argument, NULL, 'B'},
  {"context", no_argument, NULL, 'c'},
  {"directory", required_argument, NULL, 'd'},
  {"ifdef", required_argument, NULL, 'D'},
  {"ed", no_argument, NULL, 'e'},
  {"remove-empty-files", no_argument, NULL, 'E'},
  {"force", no_argument, NULL, 'f'},
  {"fuzz", required_argument, NULL, 'F'},
  {"get", required_argument, NULL, 'g'},
  {"input", required_argument, NULL, 'i'},
  {"ignore-whitespace", no_argument, NULL, 'l'},
#ifdef ENABLE_MERGE
  {"merge", optional_argument, NULL, 'm'},
#endif
  {"normal", no_argument, NULL, 'n'},
  {"forward", no_argument, NULL, 'N'},
  {"output", required_argument, NULL, 'o'},
  {"strip", required_argument, NULL, 'p'},
  {"reject-file", required_argument, NULL, 'r'},
  {"reverse", no_argument, NULL, 'R'},
  {"quiet", no_argument, NULL, 's'},
  {"silent", no_argument, NULL, 's'},
  {"batch", no_argument, NULL, 't'},
  {"set-time", no_argument, NULL, 'T'},
  {"unified", no_argument, NULL, 'u'},
  {"version", no_argument, NULL, 'v'},
  {"version-control", required_argument, NULL, 'V'},
  {"debug", required_argument, NULL, 'x'},
  {"basename-prefix", required_argument, NULL, 'Y'},
  {"suffix", required_argument, NULL, 'z'},
  {"set-utc", no_argument, NULL, 'Z'},
  {"dry-run", no_argument, NULL, CHAR_MAX + 1},
  {"verbose", no_argument, NULL, CHAR_MAX + 2},
  {"binary", no_argument, NULL, CHAR_MAX + 3},
  {"help", no_argument, NULL, CHAR_MAX + 4},
  {"backup-if-mismatch", no_argument, NULL, CHAR_MAX + 5},
  {"no-backup-if-mismatch", no_argument, NULL, CHAR_MAX + 6},
  {"posix", no_argument, NULL, CHAR_MAX + 7},
  {"quoting-style", required_argument, NULL, CHAR_MAX + 8},
  {"reject-format", required_argument, NULL, CHAR_MAX + 9},
  {"read-only", required_argument, NULL, CHAR_MAX + 10},
  {"follow-symlinks", no_argument, NULL, CHAR_MAX + 11},
  {"omnibor", optional_argument, NULL, CHAR_MAX + 12},
  {NULL, no_argument, NULL, 0}};

static char const *const option_help[] =
{
"Input options:",
"",
"  -p NUM  --strip=NUM  Strip NUM leading components from file names.",
"  -F LINES  --fuzz LINES  Set the fuzz factor to LINES for inexact matching.",
"  -l  --ignore-whitespace  Ignore white space changes between patch and input.",
"",
"  -c  --context  Interpret the patch as a context difference.",
"  -e  --ed  Interpret the patch as an ed script.",
"  -n  --normal  Interpret the patch as a normal difference.",
"  -u  --unified  Interpret the patch as a unified difference.",
"",
"  -N  --forward  Ignore patches that appear to be reversed or already applied.",
"  -R  --reverse  Assume patches were created with old and new files swapped.",
"",
"  -i PATCHFILE  --input=PATCHFILE  Read patch from PATCHFILE instead of stdin.",
"",
"Output options:",
"",
"  -o FILE  --output=FILE  Output patched files to FILE.",
"  -r FILE  --reject-file=FILE  Output rejects to FILE.",
"",
"  -D NAME  --ifdef=NAME  Make merged if-then-else output using NAME.",
#ifdef ENABLE_MERGE
"  --merge  Merge using conflict markers instead of creating reject files.",
#endif
"  -E  --remove-empty-files  Remove output files that are empty after patching.",
"",
"  -Z  --set-utc  Set times of patched files, assuming diff uses UTC (GMT).",
"  -T  --set-time  Likewise, assuming local time.",
"",
"  --quoting-style=WORD   output file names using quoting style WORD.",
"    Valid WORDs are: literal, shell, shell-always, c, escape.",
"    Default is taken from QUOTING_STYLE env variable, or 'shell' if unset.",
"",
"Backup and version control options:",
"",
"  -b  --backup  Back up the original contents of each file.",
"  --backup-if-mismatch  Back up if the patch does not match exactly.",
"  --no-backup-if-mismatch  Back up mismatches only if otherwise requested.",
"",
"  -V STYLE  --version-control=STYLE  Use STYLE version control.",
"	STYLE is either 'simple', 'numbered', or 'existing'.",
"  -B PREFIX  --prefix=PREFIX  Prepend PREFIX to backup file names.",
"  -Y PREFIX  --basename-prefix=PREFIX  Prepend PREFIX to backup file basenames.",
"  -z SUFFIX  --suffix=SUFFIX  Append SUFFIX to backup file names.",
"",
"  -g NUM  --get=NUM  Get files from RCS etc. if positive; ask if negative.",
"",
"Miscellaneous options:",
"",
"  -t  --batch  Ask no questions; skip bad-Prereq patches; assume reversed.",
"  -f  --force  Like -t, but ignore bad-Prereq patches, and assume unreversed.",
"  -s  --quiet  --silent  Work silently unless an error occurs.",
"  --verbose  Output extra information about the work being done.",
"  --dry-run  Do not actually change any files; just print what would happen.",
"  --posix  Conform to the POSIX standard.",
"",
"  -d DIR  --directory=DIR  Change the working directory to DIR first.",
"  --reject-format=FORMAT  Create 'context' or 'unified' rejects.",
"  --binary  Read and write data in binary mode.",
"  --read-only=BEHAVIOR  How to handle read-only input files: 'ignore' that they",
"                        are read-only, 'warn' (default), or 'fail'.",
"",
"  -v  --version  Output version info.",
"  --help  Output this help.",
"",
"Report bugs to <" PACKAGE_BUGREPORT ">.",
0
};

static void
usage (FILE *stream, int status)
{
  char const * const *p;

  if (status != 0)
    {
      fprintf (stream, "%s: Try '%s --help' for more information.\n",
	       program_name, Argv[0]);
    }
  else
    {
      fprintf (stream, "Usage: %s [OPTION]... [ORIGFILE [PATCHFILE]]\n\n",
	       Argv[0]);
      for (p = option_help;  *p;  p++)
	fprintf (stream, "%s\n", *p);
    }

  exit (status);
}

/* Process switches and filenames.  */

static void
get_some_switches (void)
{
    int optc;

    free (rejname);
    rejname = 0;
    if (optind == Argc)
	return;
    while ((optc = getopt_long (Argc, Argv, shortopts, longopts, (int *) 0))
	   != -1) {
	switch (optc) {
	    case 'b':
		make_backups = true;
		 /* Special hack for backward compatibility with CVS 1.9.
		    If the last 4 args are '-b SUFFIX ORIGFILE PATCHFILE',
		    treat '-b' as if it were '-b -z'.  */
		if (Argc - optind == 3
		    && strcmp (Argv[optind - 1], "-b") == 0
		    && ! (Argv[optind + 0][0] == '-' && Argv[optind + 0][1])
		    && ! (Argv[optind + 1][0] == '-' && Argv[optind + 1][1])
		    && ! (Argv[optind + 2][0] == '-' && Argv[optind + 2][1]))
		  {
		    optarg = Argv[optind++];
		    if (verbosity != SILENT)
		      say ("warning: the '-b %s' option is obsolete; use '-b -z %s' instead\n",
			   optarg, optarg);
		    goto case_z;
		  }
		break;
	    case 'B':
		if (!*optarg)
		  fatal ("backup prefix is empty");
		origprae = xstrdup (optarg);
		break;
	    case 'c':
		diff_type = CONTEXT_DIFF;
		break;
	    case 'd':
		if (chdir(optarg) < 0)
		  pfatal ("Can't change to directory %s", quotearg (optarg));
		break;
	    case 'D':
		do_defines = xstrdup (optarg);
		break;
	    case 'e':
		diff_type = ED_DIFF;
		break;
	    case 'E':
		remove_empty_files = true;
		break;
	    case 'f':
		force = true;
		break;
	    case 'F':
		maxfuzz = numeric_string (optarg, false, "fuzz factor");
		break;
	    case 'g':
		patch_get = numeric_string (optarg, true, "get option value");
		break;
	    case 'i':
		patchname = xstrdup (optarg);
		break;
	    case 'l':
		canonicalize_ws = true;
		break;
#ifdef ENABLE_MERGE
	    case 'm':
		merge = true;
		if (optarg)
		  {
		    if (! strcmp (optarg, "merge"))
		      conflict_style = MERGE_MERGE;
		    else if (! strcmp (optarg, "diff3"))
		      conflict_style = MERGE_DIFF3;
		    else
		      usage (stderr, 2);
		  }
		else
		  conflict_style = MERGE_MERGE;
		break;
#endif
	    case 'n':
		diff_type = NORMAL_DIFF;
		break;
	    case 'N':
		noreverse = true;
		break;
	    case 'o':
		outfile = xstrdup (optarg);
		break;
	    case 'p':
		strippath = numeric_string (optarg, false, "strip count");
		break;
	    case 'r':
		rejname = xstrdup (optarg);
		break;
	    case 'R':
		reverse = true;
		reverse_flag_specified = true;
		break;
	    case 's':
		verbosity = SILENT;
		break;
	    case 't':
		batch = true;
		break;
	    case 'T':
		set_time = true;
		break;
	    case 'u':
		diff_type = UNI_DIFF;
		break;
	    case 'v':
		version();
		exit (0);
		break;
	    case 'V':
		version_control = optarg;
		version_control_context = "--version-control or -V option";
		break;
#if DEBUGGING
	    case 'x':
		debug = numeric_string (optarg, true, "debugging option");
		break;
#endif
	    case 'Y':
		if (!*optarg)
		  fatal ("backup basename prefix is empty");
		origbase = xstrdup (optarg);
		break;
	    case 'z':
	    case_z:
		if (!*optarg)
		  fatal ("backup suffix is empty");
		origsuff = xstrdup (optarg);
		break;
	    case 'Z':
		set_utc = true;
		break;
	    case CHAR_MAX + 1:
		dry_run = true;
		break;
	    case CHAR_MAX + 2:
		verbosity = VERBOSE;
		break;
	    case CHAR_MAX + 3:
		no_strip_trailing_cr = true;
#if HAVE_SETMODE_DOS
		binary_transput = O_BINARY;
#endif
		break;
	    case CHAR_MAX + 4:
		usage (stdout, 0);
	    case CHAR_MAX + 5:
		backup_if_mismatch = true;
		break;
	    case CHAR_MAX + 6:
		backup_if_mismatch = false;
		break;
	    case CHAR_MAX + 7:
		posixly_correct = true;
		break;
	    case CHAR_MAX + 8:
		{
		  int i = argmatch (optarg, quoting_style_args, 0, 0);
		  if (i < 0)
		    {
		      invalid_arg ("quoting style", optarg, i);
		      usage (stderr, 2);
		    }
		  set_quoting_style ((struct quoting_options *) 0,
				     (enum quoting_style) i);
		}
		break;
	    case CHAR_MAX + 9:
		if (strcmp (optarg, "context") == 0)
		  reject_format = NEW_CONTEXT_DIFF;
		else if (strcmp (optarg, "unified") == 0)
		  reject_format = UNI_DIFF;
		else
		  usage (stderr, 2);
		break;
	    case CHAR_MAX + 10:
		if (strcmp (optarg, "ignore") == 0)
		  read_only_behavior = RO_IGNORE;
		else if (strcmp (optarg, "warn") == 0)
		  read_only_behavior = RO_WARN;
		else if (strcmp (optarg, "fail") == 0)
		  read_only_behavior = RO_FAIL;
		else
		  usage (stderr, 2);
		break;
	    case CHAR_MAX + 11:
		follow_symlinks = true;
		break;
            case CHAR_MAX + 12:
		if (optarg != NULL)
		  omnibor_option_arg = optarg;
		else
		  omnibor_option_arg = "";
		omnibor_flag = true;
		break;
            default:
		usage (stderr, 2);
	}
    }

    /* Process any filename args.  */
    if (optind < Argc)
      {
	inname = xstrdup (Argv[optind++]);
	explicit_inname = true;
	invc = -1;
	if (optind < Argc)
	  {
	    patchname = xstrdup (Argv[optind++]);
	    if (optind < Argc)
	      {
		fprintf (stderr, "%s: %s: extra operand\n",
			 program_name, quotearg (Argv[optind]));
		usage (stderr, 2);
	      }
	  }
      }
}

/* Handle STRING (possibly negative if NEGATIVE_ALLOWED is nonzero)
   of type ARGTYPE_MSGID by converting it to an integer,
   returning the result.  */
static int
numeric_string (char const *string,
		bool negative_allowed,
		char const *argtype_msgid)
{
  int value = 0;
  char const *p = string;
  int sign = *p == '-' ? -1 : 1;

  p += *p == '-' || *p == '+';

  do
    {
      int v10 = value * 10;
      int digit = *p - '0';
      int signed_digit = sign * digit;
      int next_value = v10 + signed_digit;

      if (9 < (unsigned) digit)
	fatal ("%s %s is not a number", argtype_msgid, quotearg (string));

      if (v10 / 10 != value || (next_value < v10) != (signed_digit < 0))
	fatal ("%s %s is too large", argtype_msgid, quotearg (string));

      value = next_value;
    }
  while (*++p);

  if (value < 0 && ! negative_allowed)
    fatal ("%s %s is negative", argtype_msgid, quotearg (string));

  return value;
}

/* Attempt to find the right place to apply this hunk of patch. */

static lin
locate_hunk (lin fuzz)
{
    lin first_guess = pch_first () + in_offset;
    lin offset;
    lin pat_lines = pch_ptrn_lines();
    lin prefix_context = pch_prefix_context ();
    lin suffix_context = pch_suffix_context ();
    lin context = (prefix_context < suffix_context
		   ? suffix_context : prefix_context);
    lin prefix_fuzz = fuzz + prefix_context - context;
    lin suffix_fuzz = fuzz + suffix_context - context;
    lin max_where = input_lines - (pat_lines - suffix_fuzz) + 1;
    lin min_where = last_frozen_line + 1;
    lin max_pos_offset = max_where - first_guess;
    lin max_neg_offset = first_guess - min_where;
    lin max_offset = MAX(max_pos_offset, max_neg_offset);
    lin min_offset;

    if (!pat_lines)			/* null range matches always */
	return first_guess;

    /* Do not try lines <= 0.  */
    if (first_guess <= max_neg_offset)
	max_neg_offset = first_guess - 1;

    if (prefix_fuzz < 0 && pch_first () <= 1)
      {
	/* Can only match start of file.  */

	if (suffix_fuzz < 0)
	  /* Can only match entire file.  */
	  if (pat_lines != input_lines || prefix_context < last_frozen_line)
	    return 0;

	offset = 1 - first_guess;
	if (last_frozen_line <= prefix_context
	    && offset <= max_pos_offset
	    && patch_match (first_guess, offset, 0, suffix_fuzz))
	  {
	    in_offset += offset;
	    return first_guess + offset;
	  }
	else
	  return 0;
      }
    else if (prefix_fuzz < 0)
      prefix_fuzz = 0;

    if (suffix_fuzz < 0)
      {
	/* Can only match end of file.  */
	offset = first_guess - (input_lines - pat_lines + 1);
	if (offset <= max_neg_offset
	    && patch_match (first_guess, -offset, prefix_fuzz, 0))
	  {
	    in_offset -= offset;
	    return first_guess - offset;
	  }
	else
	  return 0;
      }

    min_offset = max_pos_offset < 0 ? first_guess - max_where
	       : max_neg_offset < 0 ? first_guess - min_where
	       : 0;
    for (offset = min_offset;  offset <= max_offset;  offset++) {
	char numbuf0[LINENUM_LENGTH_BOUND + 1];
	char numbuf1[LINENUM_LENGTH_BOUND + 1];
	if (offset <= max_pos_offset
	    && patch_match (first_guess, offset, prefix_fuzz, suffix_fuzz)) {
	    if (debug & 1)
	      say ("Offset changing from %s to %s\n",
		   format_linenum (numbuf0, in_offset),
		   format_linenum (numbuf1, in_offset + offset));
	    in_offset += offset;
	    return first_guess+offset;
	}
	if (offset <= max_neg_offset
	    && patch_match (first_guess, -offset, prefix_fuzz, suffix_fuzz)) {
	    if (debug & 1)
	      say ("Offset changing from %s to %s\n",
		   format_linenum (numbuf0, in_offset),
		   format_linenum (numbuf1, in_offset - offset));
	    in_offset -= offset;
	    return first_guess-offset;
	}
    }
    return 0;
}

static void __attribute__ ((noreturn))
mangled_patch (lin old, lin new)
{
  char numbuf0[LINENUM_LENGTH_BOUND + 1];
  char numbuf1[LINENUM_LENGTH_BOUND + 1];
  if (debug & 1)
    say ("oldchar = '%c', newchar = '%c'\n",
        pch_char (old), pch_char (new));
  fatal ("Out-of-sync patch, lines %s,%s -- mangled text or line numbers, "
        "maybe?",
        format_linenum (numbuf0, pch_hunk_beg () + old),
        format_linenum (numbuf1, pch_hunk_beg () + new));
}

/* Output a line number range in unified format.  */

static void
print_unidiff_range (FILE *fp, lin start, lin count)
{
  char numbuf0[LINENUM_LENGTH_BOUND + 1];
  char numbuf1[LINENUM_LENGTH_BOUND + 1];

  switch (count)
    {
    case 0:
      fprintf (fp, "%s,0", format_linenum (numbuf0, start - 1));
      break;

    case 1:
      fprintf (fp, "%s", format_linenum (numbuf0, start));
      break;

    default:
      fprintf (fp, "%s,%s",
              format_linenum (numbuf0, start),
              format_linenum (numbuf1, count));
      break;
    }
}

static void
print_header_line (FILE *fp, const char *tag, bool reverse)
{
  const char *name = pch_name (reverse);
  const char *timestr = pch_timestr (reverse);

  fprintf (fp, "%s %s%s\n", tag, name ? name : "/dev/null",
	   timestr ? timestr : "");
}

/* Produce unified reject files */

static void
abort_hunk_unified (bool header, bool reverse)
{
  lin old = 1;
  lin lastline = pch_ptrn_lines ();
  lin new = lastline + 1;
  char const *c_function = pch_c_function();

  if (header)
    {
      if (pch_name (INDEX))
	fprintf(rejfp, "Index: %s\n", pch_name (INDEX));
      print_header_line (rejfp, "---", reverse);
      print_header_line (rejfp, "+++", ! reverse);
    }

  /* Add out_offset to guess the same as the previous successful hunk.  */
  fprintf (rejfp, "@@ -");
  print_unidiff_range (rejfp, pch_first () + out_offset, lastline);
  fprintf (rejfp, " +");
  print_unidiff_range (rejfp, pch_newfirst () + out_offset, pch_repl_lines ());
  fprintf (rejfp, " @@%s\n", c_function ? c_function : "");

  while (pch_char (new) == '=' || pch_char (new) == '\n')
    new++;

  if (diff_type != UNI_DIFF)
    pch_normalize (UNI_DIFF);

  for (; ; old++, new++)
    {
      for (;  pch_char (old) == '-';  old++)
	{
	  fputc ('-', rejfp);
	  pch_write_line (old, rejfp);
	}
      for (;  pch_char (new) == '+';  new++)
	{
	  fputc ('+', rejfp);
	  pch_write_line (new, rejfp);
	}

      if (old > lastline)
	  break;

      if (pch_char (new) != pch_char (old))
	mangled_patch (old, new);

      fputc (' ', rejfp);
      pch_write_line (old, rejfp);
    }
  if (pch_char (new) != '^')
    mangled_patch (old, new);
}

/* Output the rejected patch in context format.  */

static void
abort_hunk_context (bool header, bool reverse)
{
    lin i;
    lin pat_end = pch_end ();
    /* add in out_offset to guess the same as the previous successful hunk */
    lin oldfirst = pch_first() + out_offset;
    lin newfirst = pch_newfirst() + out_offset;
    lin oldlast = oldfirst + pch_ptrn_lines() - 1;
    lin newlast = newfirst + pch_repl_lines() - 1;
    char const *stars =
      (int) NEW_CONTEXT_DIFF <= (int) diff_type ? " ****" : "";
    char const *minuses =
      (int) NEW_CONTEXT_DIFF <= (int) diff_type ? " ----" : " -----";
    char const *c_function = pch_c_function();

    if (diff_type == UNI_DIFF)
      pch_normalize (NEW_CONTEXT_DIFF);

    if (header)
      {
	if (pch_name (INDEX))
	  fprintf(rejfp, "Index: %s\n", pch_name (INDEX));
	print_header_line (rejfp, "***", reverse);
	print_header_line (rejfp, "---", ! reverse);
      }
    fprintf(rejfp, "***************%s\n", c_function ? c_function : "");
    for (i=0; i<=pat_end; i++) {
	char numbuf0[LINENUM_LENGTH_BOUND + 1];
	char numbuf1[LINENUM_LENGTH_BOUND + 1];
	switch (pch_char(i)) {
	case '*':
	    if (oldlast < oldfirst)
		fprintf(rejfp, "*** 0%s\n", stars);
	    else if (oldlast == oldfirst)
		fprintf (rejfp, "*** %s%s\n",
			 format_linenum (numbuf0, oldfirst), stars);
	    else
		fprintf (rejfp, "*** %s,%s%s\n",
			 format_linenum (numbuf0, oldfirst),
			 format_linenum (numbuf1, oldlast), stars);
	    break;
	case '=':
	    if (newlast < newfirst)
		fprintf(rejfp, "--- 0%s\n", minuses);
	    else if (newlast == newfirst)
		fprintf (rejfp, "--- %s%s\n",
			 format_linenum (numbuf0, newfirst), minuses);
	    else
		fprintf (rejfp, "--- %s,%s%s\n",
			 format_linenum (numbuf0, newfirst),
			 format_linenum (numbuf1, newlast), minuses);
	    break;
	case ' ': case '-': case '+': case '!':
	    fprintf (rejfp, "%c ", pch_char (i));
	    /* fall into */
	case '\n':
	    pch_write_line (i, rejfp);
	    break;
	default:
	    fatal ("fatal internal error in abort_hunk_context");
	}
	if (ferror (rejfp))
	  write_fatal ();
    }
}

/* Output the rejected hunk.  */

static void
abort_hunk (char const *outname, bool header, bool reverse)
{
  if (! TMPREJNAME_needs_removal)
    init_reject (outname);
  if (reject_format == UNI_DIFF
      || (reject_format == NO_DIFF && diff_type == UNI_DIFF))
    abort_hunk_unified (header, reverse);
  else
    abort_hunk_context (header, reverse);
}

/* We found where to apply it (we hope), so do it. */

static bool
apply_hunk (struct outstate *outstate, lin where)
{
    lin old = 1;
    lin lastline = pch_ptrn_lines ();
    lin new = lastline+1;
    enum {OUTSIDE, IN_IFNDEF, IN_IFDEF, IN_ELSE} def_state = OUTSIDE;
    char const *R_do_defines = do_defines;
    lin pat_end = pch_end ();
    FILE *fp = outstate->ofp;

    where--;
    while (pch_char(new) == '=' || pch_char(new) == '\n')
	new++;

    while (old <= lastline) {
	if (pch_char(old) == '-') {
	    assert (outstate->after_newline);
	    if (! copy_till (outstate, where + old - 1))
		return false;
	    if (R_do_defines) {
		if (def_state == OUTSIDE) {
		    fprintf (fp, outstate->after_newline + not_defined,
			     R_do_defines);
		    def_state = IN_IFNDEF;
		}
		else if (def_state == IN_IFDEF) {
		    fputs (outstate->after_newline + else_defined, fp);
		    def_state = IN_ELSE;
		}
		if (ferror (fp))
		  write_fatal ();
		outstate->after_newline = pch_write_line (old, fp);
		outstate->zero_output = false;
	    }
	    last_frozen_line++;
	    old++;
	}
	else if (new > pat_end) {
	    break;
	}
	else if (pch_char(new) == '+') {
	    if (! copy_till (outstate, where + old - 1))
		return false;
	    if (R_do_defines) {
		if (def_state == IN_IFNDEF) {
		    fputs (outstate->after_newline + else_defined, fp);
		    def_state = IN_ELSE;
		}
		else if (def_state == OUTSIDE) {
		    fprintf (fp, outstate->after_newline + if_defined,
			     R_do_defines);
		    def_state = IN_IFDEF;
		}
		if (ferror (fp))
		  write_fatal ();
	    }
	    outstate->after_newline = pch_write_line (new, fp);
	    outstate->zero_output = false;
	    new++;
	}
	else if (pch_char(new) != pch_char(old))
	  mangled_patch (old, new);
	else if (pch_char(new) == '!') {
	    assert (outstate->after_newline);
	    if (! copy_till (outstate, where + old - 1))
		return false;
	    assert (outstate->after_newline);
	    if (R_do_defines) {
	       fprintf (fp, 1 + not_defined, R_do_defines);
	       if (ferror (fp))
		write_fatal ();
	       def_state = IN_IFNDEF;
	    }

	    do
	      {
		if (R_do_defines) {
		    outstate->after_newline = pch_write_line (old, fp);
		}
		last_frozen_line++;
		old++;
	      }
	    while (pch_char (old) == '!');

	    if (R_do_defines) {
		fputs (outstate->after_newline + else_defined, fp);
		if (ferror (fp))
		  write_fatal ();
		def_state = IN_ELSE;
	    }

	    do
	      {
		outstate->after_newline = pch_write_line (new, fp);
		new++;
	      }
	    while (pch_char (new) == '!');
	    outstate->zero_output = false;
	}
	else {
	    assert(pch_char(new) == ' ');
	    old++;
	    new++;
	    if (R_do_defines && def_state != OUTSIDE) {
		fputs (outstate->after_newline + end_defined, fp);
		if (ferror (fp))
		  write_fatal ();
		outstate->after_newline = true;
		def_state = OUTSIDE;
	    }
	}
    }
    if (new <= pat_end && pch_char(new) == '+') {
	if (! copy_till (outstate, where + old - 1))
	    return false;
	if (R_do_defines) {
	    if (def_state == OUTSIDE) {
		fprintf (fp, outstate->after_newline + if_defined,
			 R_do_defines);
		def_state = IN_IFDEF;
	    }
	    else if (def_state == IN_IFNDEF) {
		fputs (outstate->after_newline + else_defined, fp);
		def_state = IN_ELSE;
	    }
	    if (ferror (fp))
	      write_fatal ();
	    outstate->zero_output = false;
	}

	do
	  {
	    if (! outstate->after_newline  &&  putc ('\n', fp) == EOF)
	      write_fatal ();
	    outstate->after_newline = pch_write_line (new, fp);
	    outstate->zero_output = false;
	    new++;
	  }
	while (new <= pat_end && pch_char (new) == '+');
    }
    if (R_do_defines && def_state != OUTSIDE) {
	fputs (outstate->after_newline + end_defined, fp);
	if (ferror (fp))
	  write_fatal ();
	outstate->after_newline = true;
    }
    out_offset += pch_repl_lines() - pch_ptrn_lines ();
    return true;
}

/* Create an output file.  */

static FILE *
create_output_file (char const *name, int open_flags)
{
  int fd = create_file (name, O_WRONLY | binary_transput | open_flags,
			instat.st_mode, true);
  FILE *f = fdopen (fd, binary_transput ? "wb" : "w");
  if (! f)
    pfatal ("Can't create file %s", quotearg (name));
  return f;
}

/* Open the new file. */

static void
init_output (struct outstate *outstate)
{
  outstate->ofp = NULL;
  outstate->after_newline = true;
  outstate->zero_output = true;
}

static FILE *
open_outfile (char const *name)
{
  if (strcmp (name, "-") != 0)
    return create_output_file (name, 0);
  else
    {
      FILE *ofp;
      int stdout_dup = dup (fileno (stdout));
      if (stdout_dup == -1)
	pfatal ("Failed to duplicate standard output");
      ofp = fdopen (stdout_dup, "a");
      if (! ofp)
	pfatal ("Failed to duplicate standard output");
      if (dup2 (fileno (stderr), fileno (stdout)) == -1)
	pfatal ("Failed to redirect messages to standard error");
      /* FIXME: Do we need to switch stdout_dup into O_BINARY mode here? */
      return ofp;
    }
}

/* Open a file to put hunks we can't locate. */

static void
init_reject (char const *outname)
{
  int fd;
  fd = make_tempfile (&TMPREJNAME, 'r', outname, O_WRONLY | binary_transput,
		      0666);
  if (fd == -1)
    pfatal ("Can't create temporary file %s", TMPREJNAME);
  TMPREJNAME_needs_removal = true;
  rejfp = fdopen (fd, binary_transput ? "wb" : "w");
  if (! rejfp)
    pfatal ("Can't open stream for file %s", quotearg (TMPREJNAME));
}

/* Copy input file to output, up to wherever hunk is to be applied. */

bool
copy_till (struct outstate *outstate, lin lastline)
{
    lin R_last_frozen_line = last_frozen_line;
    FILE *fp = outstate->ofp;
    char const *s;
    size_t size;

    if (R_last_frozen_line > lastline)
      {
	say ("misordered hunks! output would be garbled\n");
	return false;
      }
    while (R_last_frozen_line < lastline)
      {
	s = ifetch (++R_last_frozen_line, false, &size);
	if (size)
	  {
	    if ((! outstate->after_newline  &&  putc ('\n', fp) == EOF)
		|| ! fwrite (s, sizeof *s, size, fp))
	      write_fatal ();
	    outstate->after_newline = s[size - 1] == '\n';
	    outstate->zero_output = false;
	  }
      }
    last_frozen_line = R_last_frozen_line;
    return true;
}

/* Finish copying the input file to the output file. */

static bool
spew_output (struct outstate *outstate, struct stat *st)
{
    if (debug & 256)
      {
	char numbuf0[LINENUM_LENGTH_BOUND + 1];
	char numbuf1[LINENUM_LENGTH_BOUND + 1];
	say ("il=%s lfl=%s\n",
	     format_linenum (numbuf0, input_lines),
	     format_linenum (numbuf1, last_frozen_line));
      }

    if (last_frozen_line < input_lines)
      if (! copy_till (outstate, input_lines))
	return false;

    if (outstate->ofp && ! outfile)
      {
	if (fflush (outstate->ofp) != 0
	    || fstat (fileno (outstate->ofp), st) != 0
	    || fclose (outstate->ofp) != 0)
	  write_fatal ();
	outstate->ofp = 0;
      }

    return true;
}

/* Does the patch pattern match at line base+offset? */

static bool
patch_match (lin base, lin offset, lin prefix_fuzz, lin suffix_fuzz)
{
    lin pline = 1 + prefix_fuzz;
    lin iline;
    lin pat_lines = pch_ptrn_lines () - suffix_fuzz;
    size_t size;
    char const *p;

    for (iline=base+offset+prefix_fuzz; pline <= pat_lines; pline++,iline++) {
	p = ifetch (iline, offset >= 0, &size);
	if (strncmp (p, "//gitoid:blob:sha1:",
		     strlen ("//gitoid:blob:sha1:")) == 0)
	  continue;
	if (canonicalize_ws) {
	    if (!similar(p, size,
			 pfetch(pline),
			 pch_line_len(pline) ))
		return false;
	}
	else if (size != pch_line_len (pline)
		 || memcmp (p, pfetch (pline), size) != 0)
	    return false;
    }
    return true;
}

/* Check if the line endings in the input file and in the patch differ. */

static bool
check_line_endings (lin where)
{
  char const *p;
  size_t size;
  bool input_crlf, patch_crlf;

  p = pfetch (1);
  size = pch_line_len (1);
  if (! size)
    return false;
  patch_crlf = size >= 2 && p[size - 2] == '\r' && p[size - 1] == '\n';

  if (! input_lines)
    return false;
  if (where > input_lines)
    where = input_lines;
  p = ifetch (where, false, &size);
  if (! size)
    return false;
  input_crlf = size >= 2 && p[size - 2] == '\r' && p[size - 1] == '\n';

  return patch_crlf != input_crlf;
}

/* Do two lines match with canonicalized white space? */

bool
similar (char const *a, size_t alen, char const *b, size_t blen)
{
  /* Ignore presence or absence of trailing newlines.  */
  alen  -=  alen && a[alen - 1] == '\n';
  blen  -=  blen && b[blen - 1] == '\n';

  for (;;)
    {
      if (!blen || (*b == ' ' || *b == '\t'))
	{
	  while (blen && (*b == ' ' || *b == '\t'))
	    b++, blen--;
	  if (alen)
	    {
	      if (!(*a == ' ' || *a == '\t'))
		return false;
	      do a++, alen--;
	      while (alen && (*a == ' ' || *a == '\t'));
	    }
	  if (!alen || !blen)
	    return alen == blen;
	}
      else if (!alen || *a++ != *b++)
	return false;
      else
	alen--, blen--;
    }
}

/* Deferred deletion of files. */

struct file_to_delete {
  char *name;
  struct stat st;
  bool backup;
};

static gl_list_t files_to_delete;

static void
init_files_to_delete (void)
{
  files_to_delete = gl_list_create_empty (GL_LINKED_LIST, NULL, NULL, NULL, true);
}

static void
delete_file_later (const char *name, const struct stat *st, bool backup)
{
  struct file_to_delete *file_to_delete;
  struct stat st_tmp;

  if (! st)
    {
      if (stat_file (name, &st_tmp) != 0)
	pfatal ("Can't get file attributes of %s %s", "file", name);
      st = &st_tmp;
    }
  file_to_delete = xmalloc (sizeof *file_to_delete);
  file_to_delete->name = xstrdup (name);
  file_to_delete->st = *st;
  file_to_delete->backup = backup;
  gl_list_add_last (files_to_delete, file_to_delete);
  insert_file_id (st, DELETE_LATER);
}

static void
delete_files (void)
{
  gl_list_iterator_t iter;
  const void *elt;

  iter = gl_list_iterator (files_to_delete);
  while (gl_list_iterator_next (&iter, &elt, NULL))
    {
      const struct file_to_delete *file_to_delete = elt;

      if (lookup_file_id (&file_to_delete->st) == DELETE_LATER)
	{
	  mode_t mode = file_to_delete->st.st_mode;

	  if (verbosity == VERBOSE)
	    say ("Removing %s %s\n",
		 S_ISLNK (mode) ? "symbolic link" : "file",
		 quotearg (file_to_delete->name));
	  move_file (0, 0, 0, file_to_delete->name, mode,
		     file_to_delete->backup);
	  removedirs (file_to_delete->name);
	}
    }
  gl_list_iterator_free (&iter);
}

/* Putting output files into place and removing them. */

struct file_to_output {
  char *from;
  struct stat from_st;
  char *to;
  mode_t mode;
  bool backup;
};

static gl_list_t files_to_output;

static void
output_file_later (char const *from, bool *from_needs_removal, const struct stat *from_st,
		   char const *to, mode_t mode, bool backup)
{
  struct file_to_output *file_to_output;

  file_to_output = xmalloc (sizeof *file_to_output);
  file_to_output->from = xstrdup (from);
  file_to_output->from_st = *from_st;
  file_to_output->to = to ? xstrdup (to) : NULL;
  file_to_output->mode = mode;
  file_to_output->backup = backup;
  gl_list_add_last (files_to_output, file_to_output);
  if (from_needs_removal)
    *from_needs_removal = false;
}

static void
output_file_now (char const *from, bool *from_needs_removal,
		 const struct stat *from_st, char const *to,
		 mode_t mode, bool backup)
{
  if (to == NULL)
    {
      if (backup)
	create_backup (from, from_st, true);
    }
  else
    {
      assert (from_st->st_size != -1);
      move_file (from, from_needs_removal, from_st, to, mode, backup);
    }
}

static void
output_file (char const *from, bool *from_needs_removal,
	     const struct stat *from_st, char const *to,
	     const struct stat *to_st, mode_t mode, bool backup)
{
  if (from == NULL)
    {
      /* Remember which files should be deleted and only delete them when the
	 entire input to patch has been processed.  This allows to correctly
	 determine for which files backup files have already been created.  */

      delete_file_later (to, to_st, backup);
    }
  else if (pch_git_diff () && pch_says_nonexistent (reverse) != 2)
    {
      /* In git-style diffs, the "before" state of each patch refers to the initial
	 state before modifying any files, input files can be referenced more than
	 once (when creating copies), and output files are modified at most once.
	 However, the input to GNU patch may consist of multiple concatenated
	 git-style diffs, which must be processed separately.  (The same output
	 file may go through multiple revisions.)

	 To implement this, we remember which files to /modify/ instead of
	 modifying the files immediately, but we create /new/ output files
	 immediately.  The new output files serve as markers to detect when a
	 file is modified more than once; this allows to recognize most
	 concatenated git-style diffs.
      */

      output_file_later (from, from_needs_removal, from_st, to, mode, backup);
    }
  else
    output_file_now (from, from_needs_removal, from_st, to, mode, backup);
}

static void
dispose_file_to_output (const void *elt)
{
  const struct file_to_output *file_to_output = elt;

  free (file_to_output->from);
  free (file_to_output->to);
}

static void
init_files_to_output (void)
{
  files_to_output = gl_list_create_empty (GL_LINKED_LIST, NULL, NULL,
					  dispose_file_to_output, true);
}

static void
gl_list_clear (gl_list_t list)
{
  while (gl_list_size (list) > 0)
    gl_list_remove_at (list, 0);
}

static void
output_files (struct stat const *st)
{
  gl_list_iterator_t iter;
  const void *elt;

  iter = gl_list_iterator (files_to_output);
  while (gl_list_iterator_next (&iter, &elt, NULL))
    {
      const struct file_to_output *file_to_output = elt;
      bool from_needs_removal = true;
      struct stat const *from_st = &file_to_output->from_st;

      output_file_now (file_to_output->from, &from_needs_removal,
		       from_st, file_to_output->to,
		       file_to_output->mode, file_to_output->backup);
      if (file_to_output->to && from_needs_removal)
	safe_unlink (file_to_output->from);

      if (st && st->st_dev == from_st->st_dev && st->st_ino == from_st->st_ino)
	{
	  /* Free the list up to here. */
	  for (;;)
	    {
	      const void *elt2 = gl_list_get_at (files_to_output, 0);
	      gl_list_remove_at (files_to_output, 0);
	      if (elt == elt2)
		break;
	    }
	  gl_list_iterator_free (&iter);
	  return;
	}
    }
  gl_list_iterator_free (&iter);
  gl_list_clear (files_to_output);
}

/* Fatal exit with cleanup. */

void
fatal_exit (int sig)
{
  cleanup ();

  if (sig)
    exit_with_signal (sig);

  exit (2);
}

static void
remove_if_needed (char const *name, bool *needs_removal)
{
  if (*needs_removal)
    {
      safe_unlink (name);
      *needs_removal = false;
    }
}

static void
cleanup (void)
{
  remove_if_needed (TMPINNAME, &TMPINNAME_needs_removal);
  remove_if_needed (TMPOUTNAME, &TMPOUTNAME_needs_removal);
  remove_if_needed (TMPPATNAME, &TMPPATNAME_needs_removal);
  remove_if_needed (TMPREJNAME, &TMPREJNAME_needs_removal);
  output_files (NULL);
}
