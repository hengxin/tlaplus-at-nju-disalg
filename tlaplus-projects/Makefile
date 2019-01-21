# The .project files created by toolbox may mistakenly using absolute paths,
# like `/home/user/project/mycode.tla', which makes the project imported 
# improperly if the project's location changed or it was cloned by others.
# Use this script to fix it!

fix-path:
	find . -type f -name .project | xargs sed -i 's,<location>/home.*/\(.*.tla\)</location>,<location>PARENT-1-PROJECT_LOC/\1</location>,g'
