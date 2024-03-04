import sqlite3

class Database:
    '''
    The Database class uses sqlite3 to maintain a database of
    relations (tables) for a theory package.
    '''

    def __init__(self, directory, db_file_name, package_name):
        '''
        Initialize a database, creating a standard set of tables
        to hold common expressions, axioms, theorems, proof steps, etc.,
        if they do not already exist in an already-existing database.
        The database will be directory/db_file_name, where directory
        is an absolute path (currently provided in the __init__() for
        the TheoryStorage class), db_file_name is expected be a string
        of the form 'name.db', and package_name will typically be
        a string like 'proveit/logic/booleans/implication', specifying
        the theory package the database serves.
        Using directory = '' (i.e. an empty string) creates a db in
        whatever current folder the __init__() takes place from;
        in particular, use directory = '' to create a db in the
        current folder from which a Jupyter notebook is being run.

        Details involving foreign keys are still being worked out ---
        in particular, what happens when the source of a foreign key
        is deleted? For example, can we make use of automatic database
        processes to update/delete a judgment record if its underlying
        expression has been deleted from the expression table?

        The tables also do not yet implement any explicit "used by"
        attribute(s).

        The theorem table does not yet record whether or not the
        theorem is still a conjecture or has a conjecture-based proof
        or a non-conjecture-based proof. We might use an attribute
        such as 'proof_status' with possible values of 'conjecture',
        'conjecture-based', or 'complete'.

        Recall that we have only five data types to work with:
            NULL, INTEGER, REAL, TEXT, BLOB
        '''

        # Allow the directory to be empty, and if not empty then
        # with or without the ending forward slash '/'.
        if (directory != '' and directory[-1] != '/'):
            # augment directory name with a forward slash
            directory = directory + '/'
        self.file_name = db_file_name
        self.directory = directory
        self.pkg_name = package_name
        # for convenience:
        self.full_path_file_name = self.directory + self.file_name

        current_tables = self._get_list_of_tables()

        # connect to the database
        # (or create it if it doesn't already exist) 
        conn = sqlite3.connect(self.full_path_file_name)

        # create a cursor
        c = conn.cursor()

        # ========================================================== #
        # Create our tables/relations, if they don't already exist.  #
        #                                                            #
        # User should manually update the x_attributes_and_types     #
        # set of attribute/type tuples for table x whenever          #
        # changing the attributes/types structure of a table. This   #
        # then helps prompt the regeneration of the table if the     #
        # table already exists in the database but with the          #
        # incorrect attribute/type pairs.                            #
        # ========================================================== #
        
        # COMMON     #

        common_attributes_and_types = {
            ('id', 'TEXT'), ('path_name', 'TEXT'), ('name', 'TEXT'),
            ('expression', 'TEXT'), ('string_format', 'TEXT'),
            ('latex_format', 'TEXT')}
        if 'common' in current_tables:
            temp_entries = self.fetch_all('common')
            # get possibly 'old' attributes and types
            prev_common_attributes_and_types = (
                    self._get_table_attributes_and_types('common'))
            if common_attributes_and_types != prev_common_attributes_and_types:
                # table structure has changed so table should be
                # be regenerated in the database
                c.execute("DROP TABLE IF EXISTS common")

        c.execute("""CREATE TABLE IF NOT EXISTS common (
            id            TEXT NOT NULL PRIMARY KEY,
            path_name     TEXT,
            name          TEXT,
            expression    TEXT,
            string_format TEXT,
            latex_format  TEXT,
            FOREIGN KEY (expression) REFERENCES expression (id)
            )""")

        # AXIOM      #

        axiom_attributes_and_types = {
            ('id', 'TEXT'), ('path_name', 'TEXT'), ('name', 'TEXT'),
            ('judgment', 'TEXT'), ('string_format', 'TEXT'),
            ('latex_format', 'TEXT')}
        if 'axiom' in current_tables:
            # get possibly 'old' attributes and types
            prev_axiom_attributes_and_types = (
                    self._get_table_attributes_and_types('axiom'))
            if axiom_attributes_and_types != prev_axiom_attributes_and_types:
                # table structure has changed so table should be
                # be regenerated in the database
                c.execute("DROP TABLE IF EXISTS axiom")

        c.execute("""CREATE TABLE IF NOT EXISTS axiom (
            id            TEXT NOT NULL PRIMARY KEY,
            path_name     TEXT,
            name          TEXT,
            judgment      TEXT,
            string_format TEXT,
            latex_format  TEXT
            )""")

        # DEFINITION #

        definition_attributes_and_types = {
                ('name', 'TEXT'), ('expression', 'TEXT')}
        if 'definition' in current_tables:
            # get possibly 'old' attributes and types
            prev_definition_attributes_and_types = (
                    self._get_table_attributes_and_types('definition'))
            if definition_attributes_and_types != (
                    prev_definition_attributes_and_types):
                # table structure has changed so table should be
                # be regenerated in the database
                c.execute("DROP TABLE IF EXISTS definition")

        c.execute("""CREATE TABLE IF NOT EXISTS definition (
            name       TEXT,
            expression TEXT
            )""")

        #  THEOREM   #

        theorem_attributes_and_types = {
                ('id', 'TEXT'), ('path_name', 'TEXT'), ('name', 'TEXT'),
                ('judgment', 'TEXT'), ('string_format', 'TEXT'),
                ('latex_format', 'TEXT')}
        if 'theorem' in current_tables:
            # get possibly 'old' attributes and types
            prev_theorem_attributes_and_types = (
                    self._get_table_attributes_and_types('theorem'))
            if theorem_attributes_and_types != (
                    prev_theorem_attributes_and_types):
                # table structure has changed so table should be
                # be regenerated in the database
                c.execute("DROP TABLE IF EXISTS theorem")

        c.execute("""CREATE TABLE IF NOT EXISTS theorem (
            id            TEXT NOT NULL PRIMARY KEY,
            path_name     TEXT,
            name          TEXT,
            judgment      TEXT,
            string_format TEXT,
            latex_format  TEXT,
            FOREIGN KEY (judgment) REFERENCES judgment (id)
            )""")

        # PROOF_STEP #

        proof_step_attributes_and_types = {
                ('id', 'TEXT'), ('type', 'TEXT'),
                ('path_name', 'TEXT'), ('name', 'TEXT'), ('judgment', 'TEXT'),
                ('requirements', 'TEXT'), ('equality_requirements', 'TEXT'),
                ('instantiations', 'TEXT'), ('string_format', 'TEXT'),
                ('latex_format', 'TEXT')}
        if 'proof_step' in current_tables:
            # get possibly 'old' attributes and types
            prev_proof_step_attributes_and_types = (
                    self._get_table_attributes_and_types('proof_step'))
            if proof_step_attributes_and_types != (
                    prev_proof_step_attributes_and_types):
                # table structure has changed so table should be
                # be regenerated in the database
                c.execute("DROP TABLE IF EXISTS proof_step")
        
        c.execute("""CREATE TABLE IF NOT EXISTS proof_step (
            id                    TEXT NOT NULL PRIMARY KEY,
            type                  TEXT,
            path_name             TEXT,
            name                  TEXT,
            judgment              TEXT,
            requirements          TEXT,
            equality_requirements TEXT,
            instantiations        TEXT,
            string_format         TEXT,
            latex_format          TEXT,
            FOREIGN KEY (judgment) REFERENCES judgment (id)
            )""")

        #  JUDGMENT  #
    
        judgment_attributes_and_types = {
                ('id', 'TEXT'), ('expression', 'TEXT'),
                ('assumptions', 'TEXT'), ('num_lit_gens', 'INTEGER'),
                ('string_format', 'TEXT'), ('latex_format', 'TEXT')}
        if 'judgment' in current_tables:
            # get possibly 'old' attributes and types
            prev_judgment_attributes_and_types = (
                    self._get_table_attributes_and_types('judgment'))
            if judgment_attributes_and_types != (
                    prev_judgment_attributes_and_types):
                # table structure has changed so table should be
                # be regenerated in the database
                c.execute("DROP TABLE IF EXISTS judgment")

        c.execute("""CREATE TABLE IF NOT EXISTS judgment (
            id            TEXT NOT NULL PRIMARY KEY,
            expression    TEXT NOT NULL,
            assumptions   TEXT,
            num_lit_gens  INTEGER,
            string_format TEXT,
            latex_format  TEXT,
            FOREIGN KEY (expression) REFERENCES expression (id)
            )""")

        # EXPRESSION #

        expression_attributes_and_types = {
                ('id', 'TEXT'), ('subexpressions', 'TEXT'),
                ('class_path', 'TEXT'), ('core_info', 'TEXT'),
                ('style_str', 'TEXT'),('string_format', 'TEXT'),
                ('latex_format', 'TEXT'), ('ref_count', 'INTEGER')}
        if 'expression' in current_tables:
            # get possibly 'old' attributes and types
            prev_expression_attributes_and_types = (
                    self._get_table_attributes_and_types('expression'))
            if expression_attributes_and_types != (
                    prev_expression_attributes_and_types):
                # table structure has changed so table should be
                # be regenerated in the database
                c.execute("DROP TABLE IF EXISTS expression")

        # c.execute("DROP TABLE IF EXISTS expression")
        # c.execute("""CREATE TABLE expression (
        c.execute("""CREATE TABLE IF NOT EXISTS expression (
            id             TEXT NOT NULL PRIMARY KEY,
            subexpressions TEXT,
            class_path     TEXT,
            core_info      TEXT,
            style_str      TEXT,
            string_format  TEXT,
            latex_format   TEXT,
            ref_count      INTEGER
            )""")

        # Commit the commands
        conn.commit()

        # Close the connection
        conn.close()

    def insert_record(self, table, attr_value_dict):
        '''
        Insert a single new record (i.e. row) into the specified table
        in the database, with attributes (and associated attribute
        values) specified by the attr_value_dict dictionary.
        The attr_value_dict must include any and all table attributes
        that have been declared as NOT NULL. 
        A ValueError is raised if the table is not a valid table in
        the database or if the list of attributes used as keys in the
        attr_value_dict dictionary contains invalid attributes.
        If an attribute is not declared as NOT NULL, Python's None
        is an acceptable value or one can simply omit any such
        attribute:value pair (in which case the record will be inserted
        with 'NULL' as the attribute value, and eventually returned
        in Python with None as the value when retrieving records).
        Catches and returns integrity error information if record
        has a primary key already existing in table.
        '''
        
        # Check: Is the specified table a valid table in the database?
        if not self._valid_table(table):
            raise ValueError(
                ("Failed attempt to insert a record into the '{0}' table " +
                 "in database '{1}': no such table in the database.").
                format(table, self.file_name))

        # Allowing users to submit a dictionary with None value(s)
        # can create headaches if we don't first clean them out (such
        # 'null' entries will be handled automatically)
        clean_attr_value_dict = (
            {k: v for k, v in attr_value_dict.items() if v is not None})

        # the following guarantees that the attr_names and attr_values
        # are consistently ordered when used separately
        attr_names, attr_values = zip(*clean_attr_value_dict.items())

        # Check: Are the attributes valid for the table?
        for k in attr_names:
            if not self._valid_attribute(table, k):
                raise ValueError(
                    ("Failed attempt to insert a record in the '{0}' table " +
                    "in database '{1}'. The table '{0}' has no attribute " +
                    "'{2}'.").format(table, self.file_name, k))

        # More sophisticated check might eventually be useful as well:
        # check that each attribute value has the correct type (TBA).

        # Connect to database and create a cursor
        conn = sqlite3.connect(self.full_path_file_name)
        c = conn.cursor()

        # Insert attribute values into the specified table.
        # We do this inside try/except block to catch a database
        # IntegrityError but still allow the database to be
        # successfully closed afterward.
        try:
            c.execute("INSERT INTO '{0}' {1} VALUES {2}".
                      format(table, str(attr_names), str(attr_values)))
        except Exception as the_exception:
            print("Database Exception: {}".format(the_exception))
            print("Database insertion unsuccessful.")

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()

    def update_records(self, table, dict_for_id=None, dict_for_setting=None):
        '''
        Update zero or more records (i.e. one or more rows) in the
        specified table in the database, identifying the record(s) by
        the conjunction of the table attribute/value pairs supplied
        in the dict_for_id dictionary, and updating the record
        attribute/value pairs specified in the dict_for_setting
        dictionary. If the dict_for_id dictionary is None or empty,
        ALL records in the table will be updated.
        Table attribute names should be specified as strings (i.e.
        with quotation marks); attribute values should be either None
        or of type INTEGER, REAL, or TEXT (i.e. string). For example,
        in a table called 'customers' containing (TEXT) attributes
        last_name, first_name, and (INTEGER) attribute telephone_num,
        calling the following:

            update_record(
                'customers',
                {'last_name':'Brown', 'telephone_num':1234},
                {'first_name':'Bobby'})

        will UPDATE records that have both (i.e. simultanously) a
        last_name attribute value of 'Brown' and a telephone_num
        attribute value of 1234 in the table 'customers', to then have
        a first_name attribute value of 'Bobby'. 

        The table must be an actual table in the database, and all
        attributes must be actual attributes of the table, else a
        ValueError is raised.

        Updating a non-existent record will NOT raise an error.
        '''

        # Check that the dict_for_setting dictionary is not empty
        # (otherwise, there is nothing to update)
        if dict_for_setting is None or len(dict_for_setting)==0:
            raise ValueError(
                ("Failed attempt to update record(s) in the '{0}' table " +
                 "in database '{1}': no attribute/value dictionary supplied " +
                 "to specify updating.").
                format(table, self.file_name))

        # Check: Is the specified table a valid table in the database?
        if not self._valid_table(table):
            raise ValueError(
                ("Failed attempt to update a record or records from " +
                 "the '{0}' table in database '{1}': " +
                 "no such table in the database.").
                format(table, self.file_name))

        # Check: Are the identifying attributes valid for the table?
        if dict_for_id is not None:
            for k in dict_for_id.keys():
                if not self._valid_attribute(table, k):
                    raise ValueError(
                        ("Failed attempt to update record in the '{0}' table " +
                        "in database '{1}'. The '{0}' table has no attribute " +
                        "'{2}' for identifying the record.").
                        format(table, self.file_name, k))

        # Check: Are the attributes-to-set valid for the table?
        for k in dict_for_setting.keys():
            if not self._valid_attribute(table, k):
                raise ValueError(
                    ("Failed attempt to update record in the '{0}' table " +
                    "in database '{1}'. The '{0}' table has no attribute " +
                    "'{2}' to set.").format(table, self.file_name, k))

        # Construct the command string: Beginning and SET portion
        command_str = ""
        for idx, (attr,attr_value) in enumerate(dict_for_setting.items()):
            if isinstance(attr_value, str):
                # need to make the quotation marks explicit
                attr_value = "\'" + str(attr_value) + "\'"
            if idx == 0:
                if attr_value is not None:
                    command_str = (
                        ("UPDATE {table} SET " +
                         "{attr}={attr_value}").
                         format(table=table, attr=attr,
                               attr_value=attr_value))
                else:
                    command_str = (
                        ("UPDATE {table} SET " +
                         "{attr}=NULL").
                         format(table=table, attr=attr))
            else:
                if attr_value is not None:
                    command_str = (
                        command_str + ", {attr}={attr_value}".
                        format(attr=attr, attr_value=attr_value))
                else:
                    command_str = (
                        command_str + ", {attr}=NULL".
                        format(attr=attr))

        # Continue constructing the command string: WHERE portion
        if dict_for_id is not None and len(dict_for_id) != 0:
            # then we limit the update(s) to particular records
            for idx, (attr,attr_value) in enumerate(dict_for_id.items()):
                if isinstance(attr_value, str):
                    # need to make the quotation marks explicit
                    attr_value = "\'" + str(attr_value) + "\'"
                if idx == 0:
                    if attr_value is not None:
                        command_str += ((
                            " WHERE {attr}={attr_value}").
                            format(attr=attr, attr_value=attr_value))
                    else:
                        command_str += ((
                            " WHERE {attr} is null").
                            format(attr=attr))
                else:
                    if attr_value is not None:
                        command_str += ((
                            ", {attr}={attr_value}").
                            format(attr=attr, attr_value=attr_value))
                    else:
                        command_str += ((
                            ", {attr} is null").
                            format(attr=attr))

        # Connect to database and create a cursor
        conn = sqlite3.connect(self.full_path_file_name)
        c = conn.cursor()

        # Update record(s) from the specified table
        c.execute(command_str)

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()

    def delete_records(self, table, attr_value_dict=None):
        '''
        Delete zero or more records (i.e. one or more rows) from the
        specified table in the database, identifying the records by the
        conjunction of the attribute:value pairs in the
        attr_value_dict dictionary.
        Table attribute names should be specified as strings;
        attribute values should be either None (without quotes) or of
        type INTEGER, REAL, or TEXT (i.e. string). For example, in a
        table called 'customers' containing (TEXT) attributes last_name,
        first_name, and (INTEGER) attribute telephone_num, calling the
        following:

            delete_record('customers',
                {'last_name':'Brown', 'telephone_num':1234})

        will delete ALL records in the customers table that have both
        (i.e. simultanously) a last_name value of 'Brown' and a
        telephone_num value of 1234 in the table 'customers'.
        The table must be an actual table in the database, and all
        attributes must be actual attributes of the table, else a
        ValueError is raised. If the attr_value_dict dictionary is
        empty or None, ALL records in the specific table will be
        deleted (but the table itself will remain, just empty).
        Deleting a non-existent record will NOT raise an error.
        '''

        # Check: Is the specified table a valid table in the database?
        if not self._valid_table(table):
            raise ValueError(
                ("Failed attempt to delete a record or records from " +
                 "the '{0}' table in database '{1}': " +
                 "no such table in the database.").
                format(table, self.file_name))

        # Check: Are the attributes valid for the table?
        for k in attr_value_dict.keys():
            if not self._valid_attribute(table, k):
                raise ValueError(
                    ("Failed attempt to check for record in the '{0}' table " +
                    "in database '{1}'. The table '{0}' has no attribute " +
                    "'{2}'.").format(table, self.file_name, k))

        # Construct the command string.
        command_str = ""
        if attr_value_dict is None or len(attr_value_dict)==0:
            # no record specifications suplied,
            # so delete all rows of the specified table
            command_str += "DELETE FROM " + table
        else:
            for idx, (attr,attr_value) in enumerate(attr_value_dict.items()):
                if isinstance(attr_value, str):
                    # need to make the quotation marks explicit
                    attr_value = "\'" + str(attr_value) + "\'"
                if idx == 0:
                    if attr_value is not None:
                        command_str = (
                            ("DELETE FROM {table} " +
                             " WHERE ({attr}={attr_value}").
                             format(table=table, attr=attr,
                                   attr_value=attr_value))
                    else:
                        command_str = (
                            ("DELETE FROM {table} " +
                             " WHERE ({attr} is null").
                             format(table=table, attr=attr))
                else:
                    if attr_value is not None:
                        command_str = (
                            command_str + " AND {attr}={attr_value}".
                            format(attr=attr, attr_value=attr_value))
                    else:
                        command_str = (
                            command_str + " AND {attr} is null".
                            format(attr=attr))
            command_str = command_str + ")"

        conn = sqlite3.connect(self.full_path_file_name)
        c = conn.cursor()

        # Delete record(s) from the specified table by executing
        # the constructed command string
        c.execute(command_str)

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()

    def retrieve_records(
            self, table, attr_value_dict_for_id=None, attr_names=None):
        '''
        Retrieve zero or more records (i.e. one or more rows) from the
        specified table in the database, identifying the record(s) by
        the conjunction of the table attribute/value pairs supplied
        in the attr_value_dict_for_id dictionary, and return the values
        for just the attributes listed in the attr_names list.
        Table attribute names should be specified with quotation
        marks (i.e. as strings) and attribute values should be either
        None or of type INTEGER, REAL, or TEXT (i.e. string).
        For example, in a table called 'customers' containing (TEXT)
        attributes last_name, first_name, and (INTEGER) attribute
        telephone_num, calling the following:

            retrieve_records(
                'customers',
                {'last_name':'Brown', 'telephone_num':1234},
                ['first_name', 'telephone_num'])

        will retrieve ALL the first name, telephone combinations for
        all records that have both (i.e. simultanously) a last_name
        attribute of 'Brown' and a telephone_num attribute of 1234 in
        the table 'customers'. The data returned is in the form of
        a list of tuples of the requested info; in the example above,
        it might look like

            [('Bobby', 1234), ('Jerry', 1234), ('James', 1234)]

        If the attr_value_dict_for_id dictionary is None or empty, all
        records in the table will be returned. If attributes list is
        None or empty, then all attributes will be returned for any
        records found.

        The table must be an actual table in the database, and all
        attributes must be actual attributes of the table, else a
        ValueError is raised.
        Retrieving a non-existent record will NOT raise an error;
        instead it will return an empty list.
        '''

        # Check: Is the specified table a valid table in the database?
        if not self._valid_table(table):
            raise ValueError(
                ("Failed attempt to retrieve a record or records from " +
                 "the '{0}' table in database '{1}': " +
                 "no such table in the database.").
                format(table, self.file_name))

        # Check: Are the identifying attributes valid for the table?
        if (attr_value_dict_for_id is not None
            and len(attr_value_dict_for_id) > 0):
            for k in attr_value_dict_for_id.keys():
                if not self._valid_attribute(table, k):
                    raise ValueError(
                        ("Failed attempt to retrieve a record or records " +
                         "from the '{0}' table in database '{1}'. " +
                         "The table '{0}' has no attribute " +
                         "'{2}'.").format(table, self.file_name, k))

        # Check: Are the attributes-to-return valid for the table?
        if attr_names is not None and len(attr_names) > 0:
            for k in attr_names:
                if not self._valid_attribute(table, k):
                    raise ValueError(
                        ("Failed attempt to retrieve a record or records "+
                         "from the '{0}' table in database '{1}'. "
                         "The table '{0}' has no attribute " +
                        "'{2}'.").format(table, self.file_name, k))

        # Construct the SELECT portion of the command string (which
        # depends on attr_names list supplied).
        command_str = ""
        if (attr_names is None or len(attr_names)==0):
            # we select all attributes in the table
            command_str = ("SELECT * FROM {table}".format(table=table))
        else:
            # we select only specified attributes from table
            attr_str = "" + attr_names[-1] + " "
            for attr_name in reversed(attr_names[:-1]):
                attr_str = attr_name + ", " + attr_str
            command_str += ("SELECT " + attr_str + "FROM {table}".
                           format(table=table))

        # Construct the WHERE portion of the command string (which
        # depends on the attr_value_dict_for_id dictionary supplied)
        if (attr_value_dict_for_id is not None
            and len(attr_value_dict_for_id)>0):
            for idx, (attr,attr_value) in enumerate(
                    attr_value_dict_for_id.items()):
                if isinstance(attr_value, str):
                    # need to make the quotation marks explicit
                    attr_value = "\'" + str(attr_value) + "\'"
                if idx == 0:
                    if attr_value is not None:
                        command_str += ((
                            " WHERE {attr}={attr_value}").
                            format(attr=attr, attr_value=attr_value))
                    else:
                        command_str += ((
                            " WHERE {attr} is null").
                            format(attr=attr))
                else:
                    if attr_value is not None:
                        command_str += ((
                            " AND {attr}={attr_value}").
                            format(attr=attr, attr_value=attr_value))
                    else:
                        command_str += ((
                            " AND {attr} is null").
                            format(attr=attr))

        # Connect to database and create a cursor
        conn = sqlite3.connect(self.full_path_file_name)
        c = conn.cursor()

        # Retrieve record(s) from the specified table by executing
        # the constructed command string and fetching results
        c.execute(command_str)
        items = c.fetchall()

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()

        return items


    def fetch_all(self, table, attr_names=None, **kwargs):
        # Query the db, returning all records in the specified table,
        # in the form of a list of tuples (each tuple corresponding
        # to a record). attr_names is an optional list of attributes
        # to select from the table (instead of just including
        # all possible attribute columns). Optional kwargs can
        # eventually be used (not yet implemented) to restrict
        # retrieval by specifying attribute values.
        # (Currently a convenience method; to be updated later.)

        # Create the command string (depends on attr_names supplied).
        command_str = ""
        if (attr_names is None or len(attr_names)==0):
            command_str = ("SELECT rowid, * FROM {table}".
                          format(table=table))
        else:
            attr_str = "" + attr_names[-1] + " "
            for attr_name in reversed(attr_names[:-1]):
                attr_str = attr_name + ", " + attr_str
            command_str += ("SELECT " + attr_str + "FROM {table}".
                           format(table=table))

        # Connect to database
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()

        # Execute command and fetch items
        c.execute(command_str)
        items = c.fetchall()

        # Close our connection
        conn.close()

        return items

    def check_for_record(self, table, attr_value_dict=None):
        '''
        A minimal check for the existence of a record, with one or more
        attributes and corresponding values specified by items in the
        attr_value_dict dictionary.
        Returns True if such a record exists and False if not.
        table should be a string specifying a valid table in self.
        Table attribute names should be specified as strings;
        attribute values should be either None or of type
        INTEGER, REAL, or TEXT (i.e. string). For example,

            self.check_for_record(
                    'passenger', {'first_name':'Bob', 'b_year':1961})

        would check the passenger table for an entry where the
        first_name attribute would be the string 'Bob' and the
        b_year attribute would be the integer 1961.
        If the attr_value_dict dictionary is None or empty, the method
        simply checks for the existence of any records at all in the
        specified table.
        '''

        # Check: Is the specified table a valid table in the database?
        if not self._valid_table(table):
            raise ValueError(
                ("Failed attempt to check for record in the '{0}' table " +
                 "in database '{1}': no such table in the database.").
                format(table, self.file_name))

        # Check: Are the identifying attributes (if any) valid for
        #        the table?
        if attr_value_dict is not None:
            for k in attr_value_dict.keys():
                if not self._valid_attribute(table, k):
                    raise ValueError(
                        ("Failed attempt to check for record in the '{0}' " +
                         "table in database '{1}'. The '{0}' table has " +
                         "no attribute '{2}'.").
                        format(table, self.file_name, k))

        # Construct the query string. We don't care how many such
        # entries might exist, just if ANY such entry exists at all.
        query_str = ""
        if attr_value_dict is None or len(attr_value_dict)==0:
            query_str = ("SELECT EXISTS(SELECT 1 FROM {table})".
                        format(table=table))
        else:
            # attr_value_dict is not empty, so looking for more
            # detailed table entries
            for idx, (attr,attr_value) in enumerate(attr_value_dict.items()):
                if isinstance(attr_value, str):
                    # need to make the quotation marks explicit
                    attr_value = "\'" + str(attr_value) + "\'"
                if idx == 0:
                    if attr_value is not None:
                        query_str = (
                            ("SELECT EXISTS(SELECT 1 FROM {table} " +
                            " WHERE ({attr}={attr_value}").
                            format(table=table, attr=attr,
                                   attr_value=attr_value))
                    else:
                        query_str = (
                            ("SELECT EXISTS(SELECT 1 FROM {table} " +
                            " WHERE ({attr} is null").
                            format(table=table, attr=attr))
                else:
                    if attr_value is not None:
                        query_str = (
                            query_str + " AND {attr}={attr_value}".
                            format(attr=attr, attr_value=attr_value))
                    else:
                        query_str = (
                            query_str + " AND {attr} is null".
                            format(attr=attr))
            query_str = query_str + "))"

        # Connect to database and establish cursor
        conn = sqlite3.connect(self.full_path_file_name)
        c = conn.cursor()

        # Execute the query and fetch the result (result will
        # be 1 if an entry exists or 0 if no such entry exists)
        c.execute(query_str)
        result = c.fetchone()[0]

        # Close our connection
        conn.close

        # finish up
        if result == 1:
            return True
        else:
            return False

    def clear_all_records_in_table(self, table):
        # Clear all records (i.e. rows) in the specified table

        # Connect to database
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()
        # Delete all records from the specified table
        c.execute("DELETE FROM " + table)

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()

    def clear_all_records_in_database(self):
        '''
        Clear all records (i.e. all tables) in database.
        This leaves the existing tables, but leaves them empty
        of any records.
        '''
        # Get list of all tables in the database
        tables = self._get_list_of_tables()
        # Connect to database
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()
        # Delete all records from each table
        for table in tables:
            c.execute("DELETE FROM " + table)

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()

    def clear_database(self):
        '''
        Delete all tables in database (i.e., don't just clear the
        records from each table, but delete the tables themselves,
        so they must be re-created from scratch during any
        initialization procedure). This becomes important to be able
        to do if the structure of one or more tables is modified (but
        the initilization process wouldn't recreate the table if the
        original differently-structured table still existed).
        '''
        # Get list of all tables in the database
        tables = self._get_list_of_tables()
        # Connect to database
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()
        # Delete each each table (i.e. remove table from database)
        for table in tables:
            c.execute("DROP table IF EXISTS " + table)

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()


    # ==================================== #
    # Utility Functions                    #
    # ==================================== #

    def _get_list_of_tables(self):
        '''
        Return a list of the tables in the database.
        This is useful for raising informative errors, for example
        when a client tries to add a record to a non-existent table.
        '''

        # Connect to the database.
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()
        # Obtain the table names (an awkward process)
        c.execute("SELECT name from sqlite_master where type='table'")
        temp_list_of_tuples = c.fetchall()
        # temp_list_of_tuples turns out to be a list of
        # single-element tuples, so we clean things up:
        table_names = []
        for item in temp_list_of_tuples:
            table_names.append(item[0])

        # Close connection and return list of table names
        conn.close()
        return list(table_names)

    def _get_list_of_table_attributes(self, table):
        '''
        Return a list of the attributes in the given table.
        This is useful for raising informative errors, for example
        when a client tries to delete a record by specifying a value
        for an attribute that doesn't exist.
        '''

        # Connect to the database.
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()
        # Obtain the attribute names (an awkward process)
        c.execute("SELECT name FROM PRAGMA_TABLE_INFO('{0}')".
                  format(table));
        temp_list_of_tuples = c.fetchall()
        # temp_list_of_tuples turns out to be a list of
        # single-element tuples, so we clean things up:
        attribute_names = []
        for item in temp_list_of_tuples:
            attribute_names.append(item[0])

        # Close connection and return list of attribute names
        conn.close()
        return list(attribute_names)

    def _get_table_attributes_and_types(self, table):
        '''
        Return the set of (attribute, type) tuples for the given table.
        This is useful for raising informative errors, for example
        when a client tries to delete a record by specifying a value
        for an attribute that doesn't exist. This is also useful for
        checking for changes in the structure of tables during
        development.
        For example, in a database with a table called 'customers'
        containing (TEXT) attributes last_name, first_name, and
        (INTEGER) attribute telephone_num, calling the following:

            self._get_table_attributes_and_types('customers')

        will return the following set of tuples:

            {('lastname', 'TEXT'), ('first_name', 'TEXT'),
             ('telephone_num', 'INTEGER')}
        '''

        # Connect to the database.
        conn = sqlite3.connect(self.full_path_file_name)
        # Create a cursor
        c = conn.cursor()
        # Obtain the attribute names and types
        c.execute("SELECT name, type FROM PRAGMA_TABLE_INFO('{0}')".
                  format(table));
        set_of_attr_type_tuples = set(c.fetchall())

        # Close connection and return set of (attribute, type) tuples
        conn.close()
        return set_of_attr_type_tuples

    def _valid_table(self, table):
        '''
        Return True if table is a valid table in database self,
        else return False.
        '''
        return table in self._get_list_of_tables()

    def _valid_attribute(self, table, attribute):
        '''
        Return True if attribute is a valid attribute for table
        in database self, else return False. Assumes the table itself
        is valid (see _valid_table() method above).
        '''
        return attribute in self._get_list_of_table_attributes(table)

    @staticmethod
    def _parse_unique_rep(unique_rep_str):
        '''
        Given a unique representation string, unique_rep_str, returns
        the list of representations of the referenced Prove-It objects,
        organized based on the type of Prove-It object represented
        by the unique_rep_str.
        '''
        from proveit import Expression, Judgment, Proof

        # ============================================================ #
        # General Processing
        # ============================================================ #

        # split the unique_rep string by semi-colons
        _rep_str_semi_parsed = unique_rep_str.split(";")
        _id_str = _rep_str_semi_parsed[0]
        _reqs_str = _rep_str_semi_parsed[1]
        # then split the first component of that result by the first
        # 2 colons (which avoids splitting on other colons that might
        # appear there in an instantiation's substitution dictionary)

        # Other: Expression
        #   sub-expr, ..., sub-expr; class path; core info; style str 

        # ============================================================ #
        # Proof objects
        # requirement_ids appended w/* are equality requirements?
        # Unique representation strings of Proof objects will have
        # one of the following (string) formats:

        # Proof:assumption:[judgment_id];[]
        # Proof:generalization:[judgment_id];[requirement_ids]
        # Proof:instantiation:{dict}:[judgment_id];[requirement_ids]
        # Proof:modus ponens:[judgment_id];[requirement_ids]
        # Proof:axiom_axiompathname:[judgment_id];[requirement_ids]
        # Proof:theorem_theorempathname:[judgment_id];[requirement_ids]
        #
        # Notice that theorem and axiom objects are actually proof
        # object and have Proof-based unique_rep strings.
        # ============================================================ #

        if unique_rep_str[:5] == 'Proof':
            _proveit_obj = 'Proof'

            _id_str = _rep_str_semi_parsed[0]
            _mixed_reqs_str = _rep_str_semi_parsed[1].strip("[]")
            # then split the first component of _id_str by the first
            # 2 colons (which avoids splitting on other colons that
            # might appear there in an instantiation's substitution
            # dictionary)
            _id_str_parsed = _id_str.split(":", 2)
            # something strange happening if stripping "[]" produces
            # an empty string, in fact producing an empty tuple, which
            # then behaves weirdly when using split, so we check:
            if len(_mixed_reqs_str) != 0:
                _reqs_str_parsed = _mixed_reqs_str.split(",")
            else:
                _reqs_str_parsed = []

            # process requirements, separating out requirements from
            # equality replacement requirements
            _reqs_list = []
            _eq_replacement_reqs_list = []
            for requirement in _reqs_str_parsed:
                if requirement[-1]=='*':
                    _eq_replacement_reqs_list.append(requirement.strip("*"))
                else:
                    _reqs_list.append(requirement)
            if len(_reqs_list) != 0:
                _reqs_str = "[" + ",".join(_reqs_list) + "]"
            else:
                _reqs_str = None
            if len(_eq_replacement_reqs_list) != 0:
                _eq_replacement_reqs_str = (
                    "[" + ",".join(_eq_replacement_reqs_list) + "]")
            else:
                _eq_replacement_reqs_str = None

            _path_name = None
            _name      = None

            # Proof step: instantiation
            if _id_str_parsed[1] == 'instantiation':
                # then the next piece of str includes a dictionary
                _type = 'instantiation'
                dict_end_idx = _id_str_parsed[2].find("}")
                _subst_dict = _id_str_parsed[2][:dict_end_idx + 1]
                _judgment_id = _id_str_parsed[2][dict_end_idx+1:].strip("[]")
            # then all other types of proof steps
            else:
                _type = _id_str_parsed[1]
                _subst_dict = None
                _judgment_id = _id_str_parsed[2].strip("[]")
                if (_id_str_parsed[1][0:5] == 'axiom' or
                    _id_str_parsed[1][0:7] == 'theorem'):
                    _type = _id_str_parsed[1].split("_", 1)[0]
                    _path_name = _id_str_parsed[1].split("_", 1)[1]
                    _name = _id_str_parsed[1].rsplit(".", 1)[1]
                # else:
                #     _path_name = None
                #     _name = None

            return {'obj':_proveit_obj, 'type':_type, 'subst_dict':_subst_dict,
                    'judgment_id':_judgment_id, 'reqs':_reqs_str,
                    'eq_reqs':_eq_replacement_reqs_str,
                    'path_name': _path_name, 'name':_name}

        # ============================================================ #
        # Judgment objects
        # unique_rep strings of Judgment objects will have
        # the following string format:
        #
        #     'Judgment:expr_id;[assump_id_1, ..., assump_id_n]m'
        #
        # where m is the non-zero number of literal generalizations
        # (when m=0, the most common case, the value is omitted).
        # ============================================================ #

        elif unique_rep_str[:8] == 'Judgment':
            _proveit_obj = 'Judgment'
            _id_str = _rep_str_semi_parsed[0]     # 'Judgment:expr_id'
            _expr_id = _id_str.split(":")[1]      #          'expr_id'
            if _rep_str_semi_parsed[1][-1]==']':
                _assumptions_str = _rep_str_semi_parsed[1]
                _num_lit_gens = 0
            else:
                assump_end_idx = _rep_str_semi_parsed[1].find("}")
                _assumptions_str = _rep_str_semi_parsed[1][:assump_end_idx+1]
                _num_lit_gens = int(_rep_str_semi_parsed[1][assump_end_idx+1:])
            return {'obj':_proveit_obj,
                    'expr':_expr_id,
                    'assumptions':_assumptions_str,
                    'num_lit_gens':_num_lit_gens}

        # ============================================================ #
        # Expression objects
        # unique_rep strings of Expression objects will have
        # the following string format:
        #
        #     'sub_expr_info;class_path;core_info;style_str'
        #
        # For example, we might have something like this example
        # pulled (and slightly abbreviated) from the
        # physics.quantum.QPE pkg (breaking the string at commas and
        # semicolons to fit in this space):
        #
        #    proveit.logic.booleans.....common.083d2...,
        #    49c89bde7b2e90ddc64350c8088ab9227170dd910;  
        #    proveit.logic.booleans.....forall.Forall;
        #    Operation;
        #    with_wrapping:True
        #
        # Notice also that the core_info entry always ends with a
        # semi-colon, so splitting the string on ";" always produces
        # a 4th entry, though sometimes the entry is the empty string.
        # ============================================================ #

        else:
            # Assumed to be an Expression
            _proveit_obj = 'Expression'
            _sub_exprs  = '[' + _rep_str_semi_parsed[0] + ']'
            _class_path = _rep_str_semi_parsed[1]
            _core_info  = _rep_str_semi_parsed[2]
            _style_str  = _rep_str_semi_parsed[3]
            if _style_str == '':
                # The None Python type will automatically convert to the
                # desired NULL when storing into sqlite database
                _style_str = None
            return {'obj':_proveit_obj,
                    'sub_exprs':_sub_exprs,
                    'class_path':_class_path,
                    'core_info':_core_info,
                    'style_str':_style_str}
